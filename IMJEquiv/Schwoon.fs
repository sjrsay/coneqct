module IMJEquiv.Schwoon

open System
open System.Text
open System.Runtime.InteropServices
open Microsoft.FSharp.NativeInterop

type wIdent = int
type wSRvalue = IntPtr

[<DllImport("WPDS", CallingConvention=CallingConvention.Cdecl)>]
extern int wIdentCreate(string)

[<DllImport("WPDS", CallingConvention=CallingConvention.Cdecl)>]
extern void wInit()

[<DllImport("WPDS", CallingConvention=CallingConvention.Cdecl)>]
extern void wFinish()

[<DllImport("WPDS", CallingConvention=CallingConvention.Cdecl)>]
extern IntPtr nulsr()

[<DllImport("WPDS", CallingConvention=CallingConvention.Cdecl)>]
extern IntPtr wPDSCreate(IntPtr)

[<DllImport("WPDS", CallingConvention=CallingConvention.Cdecl)>]
extern void wPDSDelete(IntPtr)

[<DllImport("WPDS", CallingConvention=CallingConvention.Cdecl)>]
extern IntPtr wPDSInsert(IntPtr, wIdent, wIdent, wIdent, wIdent, wIdent, wSRvalue)

[<DllImport("WPDS", CallingConvention=CallingConvention.Cdecl)>]
extern IntPtr wFACreate(IntPtr)

[<DllImport("WPDS", CallingConvention=CallingConvention.Cdecl)>]
extern void wFADelete(IntPtr)

[<DllImport("WPDS", CallingConvention=CallingConvention.Cdecl)>]
extern IntPtr wFAInsert(IntPtr, wIdent, wIdent, wIdent, wSRvalue, IntPtr)

[<DllImport("WPDS", CallingConvention=CallingConvention.Cdecl)>]
extern IntPtr wPrestar(IntPtr, IntPtr, sbyte)

[<DllImport("WPDS", CallingConvention=CallingConvention.Cdecl)>]
extern IntPtr wFAFind(IntPtr, wIdent, wIdent, wIdent)
