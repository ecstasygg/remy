asm {
_REMY::
    PUSH RBP
    MOV RBP,RSP
    MOV RAX,U64 SF_ARG1[RBP]
    MOV R8,U64 SF_ARG2[RBP]
    MOV R9,U64 SF_ARG3[RBP]
    MOV RDX,U64 SF_ARG4[RBP]
    CALL RAX
    POP RBP
    RET1 32
}

_extern _REMY U64 Pixel(U8 *code,U64 x,U64 y,U64 t);

U8 *names[3]={"Rings","Weave","Cells"};
CDC *image=NULL;
U8 *shader=NULL;
U8 *program=NULL;
I64 selected;
U8 *directory="C:/";
U8 *incoming=NULL;
I64 received=0,expected=0;
U32 synchronise=0,revision=0;
I64 display_lock=0,reply_lock=0,transfer=0;
CTask *receiver=NULL;
Bool live_mode=FALSE;
F64 last_received;

U0 Reply(U32 sequence,U32 status)
{
    U32 words[4];
    I64 i;
    F64 until;
    U8 *bytes=words;
    while (LBts(&reply_lock,0)) Yield;
    words[0]=0x31414D52;
    words[1]=sequence;
    words[2]=status;
    words[3]=revision;
    for (i=0;i<16;i++) {
        until=tS()+0.1;
        while (!(InU8(0x3FD)&0x20)) {
            if (tS()>until) {
                LBtr(&reply_lock,0);
                return;
            }
        }
        OutU8(0x3F8,bytes[i]);
    }
    LBtr(&reply_lock,0);
}

U64 Checksum(U8 *bytes,I64 size,U64 value=14695981039346656037)
{
    I64 i;
    for (i=0;i<size;i++) value=(value^bytes[i])*1099511628211;
    return value;
}

U0 Accept()
{
    U32 *header=incoming;
    U64 sum,*rows;
    U8 *next_code=NULL,*next_source=NULL,*old_code,*old_source;
    I64 i;
    Bool matches=TRUE;
    sum=Checksum(incoming,20);
    sum=Checksum(incoming+28,expected-28,sum);
    if (sum!=*(incoming+20)(U64 *)) {
        Reply(header[4],2);
        return;
    }
    if (header[4]==revision) {
        Reply(header[4],1);
        return;
    }
    try {
        next_code=MAlloc(header[1]);
        next_source=CAlloc(header[2]+1);
        MemCpy(next_code,incoming+28,header[1]);
        MemCpy(next_source,incoming+28+header[1],header[2]);
        rows=(incoming+28+header[1]+header[2])(U64 *);
        for (i=0;i<512;i++) {
            if (Pixel(next_code,rows[4*i],rows[4*i+1],rows[4*i+2])!=rows[4*i+3]) {
                matches=FALSE;
                break;
            }
        }
        if (matches) {
            while (LBts(&display_lock,0)) Yield;
            old_code=shader;
            old_source=program;
            shader=next_code;
            program=next_source;
            next_code=NULL;
            next_source=NULL;
            revision=header[4];
            LBtr(&display_lock,0);
            Free(old_code);
            Free(old_source);
            Reply(header[4],1);
        } else Reply(header[4],3);
        Free(next_code);
        Free(next_source);
    } catch {
        Free(next_code);
        Free(next_source);
        Reply(header[4],3);
    }
}

U0 Poll()
{
    I64 i;
    U64 byte;
    F64 until;
    U32 *header=incoming;
    if (received && tS()-last_received>5) {
        received=0;
        expected=0;
        synchronise=0;
    }
    if (!(InU8(0x3FD)&1)) return;
    until=tS()+0.004;
    for (i=0;i<8192;) {
        if (!(InU8(0x3FD)&1)) {
            if (tS()>=until) break;
            goto skip;
        }
        byte=InU8(0x3F8)&255;
        i++;
        last_received=tS();
        if (received<4) {
            synchronise=(synchronise>>8)|(byte(U32)<<24);
            if (synchronise==0x31594D52) {
                header[0]=synchronise;
                received=4;
            }
            goto skip;
        }
        incoming[received++]=byte;
        if (received==28) {
            if (!header[1] || header[1]>65536 || !header[2] || header[2]>65536 ||
                header[3]!=512 || !header[4]) {
                Reply(header[4],4);
                received=0;
                expected=0;
                synchronise=0;
                goto skip;
            }
            expected=28+header[1]+header[2]+16384;
        }
        if (expected && received==expected) {
            LBts(&transfer,0);
            break;
        }
skip:;
    }
}

U0 Receive(U8 *)
{
    while (TRUE) {
        if (Bt(&transfer,0)) Sleep(1);
        else {
            Poll();
            if (!received) Sleep(1);
            else Yield;
        }
    }
}

Bool Verify()
{
    I64 i,j,size,total=0;
    U8 *code=NULL,path[64];
    U64 *rows=NULL;
    try {
        for (i=0;i<3;i++) {
            StrPrint(path,"%s%s.BIN",directory,names[i]);
            code=FileRead(path,&size);
            if (!code) throw('Code');
            "%-6s  %d bytes  ",names[i],size;
            StrPrint(path,"%s%s.DAT",directory,names[i]);
            rows=FileRead(path,&size);
            if (!rows || size!=16384) throw('Vectors');
            for (j=0;j<size/32;j++) {
                if (Pixel(code,rows[4*j],rows[4*j+1],rows[4*j+2])!=rows[4*j+3]) {
                    throw('Mismatch');
                }
                total++;
            }
            "%d comparisons passed\n",size/32;
            Free(rows);
            rows=NULL;
            Free(code);
            code=NULL;
        }
    } catch {
        Free(rows);
        Free(code);
        "verification failed after %d cases\n",total;
        return FALSE;
    }
    "native results match HOL evaluation (%d cases)\n",total;
    return TRUE;
}

U0 Draw(CTask *,CDC *dc)
{
    U8 *title="live";
    if (!live_mode) title=names[selected];
    if (LBts(&display_lock,0)) return;
    try {
        dc->color=BLUE;
        GrPrint(dc,80,24,"remy  %s  revision %d",title,revision);
        dc->color=BLACK;
        GrBlot(dc,80,64,image);
        GrPrint(dc,80,416,"%s",program);
        LBtr(&display_lock,0);
    } catch {
        LBtr(&display_lock,0);
    }
}

U0 Release(Bool restore)
{
    Fs->draw_it=NULL;
    if (receiver) {
        Kill(receiver);
        receiver=NULL;
    }
    while (LBts(&display_lock,0)) Yield;
    if (restore) SettingsPop;
    DCDel(image);
    image=NULL;
    Free(shader);
    shader=NULL;
    Free(program);
    program=NULL;
    Free(incoming);
    incoming=NULL;
    LBtr(&display_lock,0);
}

U0 Show(I64 which=0,Bool live=FALSE)
{
    I64 x,y,dy,t=0,cpu=0,key;
    U8 color,path[64];
    Bool restore=FALSE;
    if (!(0<=which<3)) return;
    try {
        selected=which;
        live_mode=live;
        StrPrint(path,"%s%s.BIN",directory,names[which]);
        shader=FileRead(path);
        if (!shader) throw('Code');
        StrPrint(path,"%s%s.TXT",directory,names[which]);
        program=FileRead(path);
        if (!program) throw('Source');
        image=DCNew(480,336);
        if (live) {
            incoming=CAlloc(147484);
            received=0;
            expected=0;
            synchronise=0;
            revision=0;
            OutU8(0x3F9,0);
            OutU8(0x3FB,0x80);
            OutU8(0x3F8,1);
            OutU8(0x3F9,0);
            OutU8(0x3FB,3);
            OutU8(0x3FA,7);
            OutU8(0x3FC,3);
            transfer=0;
            if (mp_cnt>1) cpu=1;
            receiver=Spawn(&Receive,NULL,"remy uart",cpu);
            if (!receiver) throw('Receiver');
            Reply(0,0);
        }
        SettingsPush;
        restore=TRUE;
        AutoComplete(OFF);
        WinMax;
        DocClear;
        FlushMsgs;
        Fs->draw_it=&Draw;
        while (TRUE) {
            key=ScanChar();
            if (key && (!live || key==CH_ESC)) break;
            if (live && Bt(&transfer,0)) {
                Accept();
                received=0;
                expected=0;
                synchronise=0;
                LBtr(&transfer,0);
            }
            for (y=0;y<112;y++) {
                for (x=0;x<160;x++) {
                    color=Pixel(shader,x,y,t)&15;
                    for (dy=0;dy<3;dy++)
                        MemSet(image->body+(3*y+dy)*480+3*x,color,3);
                }
            }
            t+=2;
            Refresh;
            Sleep(20);
        }
    } catch {
        PutExcept;
        Release(restore);
        return;
    }
    Release(restore);
    DocClear;
}

U0 Live(I64 which=0)
{
    Show(which,TRUE);
}
