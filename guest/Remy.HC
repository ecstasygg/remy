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

U0 Verify()
{
    I64 i,j,size,total=0;
    U8 *code=NULL,path[64];
    U64 *rows=NULL;
    try {
        for (i=0;i<3;i++) {
            StrPrint(path,"C:/%s.BIN",names[i]);
            code=FileRead(path,&size);
            if (!code) throw('Code');
            "%-6s  %d bytes  ",names[i],size;
            StrPrint(path,"C:/%s.DAT",names[i]);
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
    }
    "native results match HOL evaluation (%d cases)\n",total;
}

U0 Draw(CTask *,CDC *dc)
{
    dc->color=BLUE;
    GrPrint(dc,80,24,"remy  %s",names[selected]);
    dc->color=BLACK;
    GrBlot(dc,80,64,image);
    GrPrint(dc,80,416,"%s",program);
}

U0 Release(Bool restore)
{
    Fs->draw_it=NULL;
    if (restore) SettingsPop;
    DCDel(image);
    image=NULL;
    Free(shader);
    shader=NULL;
    Free(program);
    program=NULL;
}

U0 Show(I64 which=0)
{
    I64 x,y,dy,t=0;
    U8 color,path[64];
    Bool restore=FALSE;
    if (!(0<=which<3)) return;
    try {
        selected=which;
        StrPrint(path,"C:/%s.BIN",names[which]);
        shader=FileRead(path);
        if (!shader) throw('Code');
        StrPrint(path,"C:/%s.TXT",names[which]);
        program=FileRead(path);
        if (!program) throw('Source');
        image=DCNew(480,336);
        SettingsPush;
        restore=TRUE;
        AutoComplete(OFF);
        WinMax;
        DocClear;
        Fs->draw_it=&Draw;
        while (!ScanChar) {
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
        Release(restore);
    }
    Release(restore);
    DocClear;
}
