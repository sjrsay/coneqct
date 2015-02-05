module IMJEquiv.Schwoon

open System
open System.Text
open System.Runtime.InteropServices
open Microsoft.FSharp.NativeInterop

type wIdent = int
type wSRvalue = IntPtr

type TRACE =
  | TRACE_NO = 0
  | TRACE_COPY = 1
  | TRACE_REF = 2
  | TRACE_REF_TOTAL = 3

[<DllImport("WPDS.dll", CallingConvention=CallingConvention.Cdecl)>]
extern int wIdentCreate(string)

[<DllImport("WPDS.dll", CallingConvention=CallingConvention.Cdecl)>]
extern void wInit()

[<DllImport("WPDS.dll", CallingConvention=CallingConvention.Cdecl)>]
extern void wFinish()

[<DllImport("WPDS.dll", CallingConvention=CallingConvention.Cdecl)>]
extern IntPtr nulsr()

[<DllImport("WPDS.dll", CallingConvention=CallingConvention.Cdecl)>]
extern IntPtr wPDSCreate(IntPtr)

[<DllImport("WPDS.dll", CallingConvention=CallingConvention.Cdecl)>]
extern void wPDSDelete(IntPtr)

[<DllImport("WPDS.dll", CallingConvention=CallingConvention.Cdecl)>]
extern IntPtr wPDSInsert(IntPtr, wIdent, wIdent, wIdent, wIdent, wIdent, wSRvalue)

[<DllImport("WPDS.dll", CallingConvention=CallingConvention.Cdecl)>]
extern IntPtr wFACreate(IntPtr)

[<DllImport("WPDS.dll", CallingConvention=CallingConvention.Cdecl)>]
extern void wFADelete(IntPtr)

[<DllImport("WPDS.dll", CallingConvention=CallingConvention.Cdecl)>]
extern IntPtr wFAInsert(IntPtr, wIdent, wIdent, wIdent, wSRvalue, IntPtr)

[<DllImport("WPDS.dll", CallingConvention=CallingConvention.Cdecl)>]
extern IntPtr wPrestar(IntPtr, IntPtr, sbyte)

[<DllImport("WPDS.dll", CallingConvention=CallingConvention.Cdecl)>]
extern IntPtr wFAFind(IntPtr, wIdent, wIdent, wIdent)
