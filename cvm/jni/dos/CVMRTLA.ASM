.model tiny
.stack 100h
.code

cvmind:
 db ': PLUS + ; ', 0

cvminp:
 dw cvmind

crd:
 dw 0
 
public _mygetchar
_mygetchar proc
 push bx
 ; push cx
 push dx
 ; jmp zero1
 mov bx,[word ptr cvminp]
 cmp bx,0
 jz zero1
 mov al,[bx]
 cmp al,0
 jz zero2
 mov ah,0
 inc bx
 mov [word ptr cvminp],bx
 mov [word ptr crd],ax
 ; mov cx,ax
 ; mov dx,ax
 ; mov ah,2
 ; int 21h
 ; mov ah,1
 ; int 21h
 ; mov dx,[word ptr crd]
 ; mov ah,2
 ; int 21h
 ; jmp zero1
 ; mov ax,[word ptr crd]
 ; mov ax,cx
 ; mov ax,20h
 jmp endmgc
zero2:
 mov ax,0
 mov [word ptr cvminp],ax
zero1:
 mov ah, 1
 int 21h
 mov ah, 0
endmgc:
 pop dx
 ; pop cx
 pop bx
 ret
 _mygetchar endp

public _my1getchar
_my1getchar proc
 mov ah, 1
 int 21h
 mov ah, 0
 ret
 _my1getchar endp

public _myputchar
_myputchar proc
 push bp
 mov bp,sp
 mov dx,[bp+4]
 mov ah,2
 int 21h
 pop bp
 ret
 _myputchar endp

public _myexit
_myexit proc
 mov ah,0
 int 21h
 ret
 _myexit endp

public _fillmem
_fillmem proc
 push bx
 push cx
 push si
 mov bx,sp
 mov si,[bx+6]
 mov cl,[si]
 mov ch,0
 inc si
 cld
 rep movsb
 mov [bx+6],si
 pop si
 pop cx
 pop bx
 ret
 _fillmem endp 

public _f_fopen
_f_fopen proc
 mov ah,3Dh
 int 21h
 ret
 _f_fopen endp

public _f_fclose
_f_fclose proc
 mov bx,ax
 mov ah,3Eh
 int 21h
 ret
 _f_fclose endp

filebuf: db 0

public _f_fgetc
_f_fgetc proc
 mov bx,ax
 mov ah,3Fh
 mov cx,1
 lea dx,filebuf
 int 21h
 mov al,[byte ptr filebuf]
 mov ah,0
 ret
 _f_fgetc endp

public _f_fputc
_f_fputc proc
 mov [byte ptr filebuf],dl
 mov bx,ax
 mov ah,40h
 mov cx,1
 lea dx,filebuf
 int 21h
 ret
 _f_fputc endp

end


