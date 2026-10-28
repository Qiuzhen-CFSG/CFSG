module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.Shared.Mixed.Sums05

/-!
# Rows 0–223 of mixed product gate 4

Certificates for the literal HSG1-f4r896aB0 candidates. The generator
proposes witnesses only; all arithmetic equalities are checked by the kernel.
Source attribution and conventions: `TracePair/source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Shared.Mixed.Gate04
open Representation.HigmanSims.LargeModels.TracePair.Certificates
open Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.LinearCertificates

open Sums05

private noncomputable def witness000 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row003

private theorem row000 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 0 (0, 0)) ((rowsAt 6).getD 0 (0, 0)) := by
  apply of_certificate witness000
  · decide +kernel
  · decide +kernel

private noncomputable def witness001 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row002

private theorem row001 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 1 (0, 0)) ((rowsAt 6).getD 1 (0, 0)) := by
  apply of_certificate witness001
  · decide +kernel
  · decide +kernel

private noncomputable def witness002 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row007

private theorem row002 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 2 (0, 0)) ((rowsAt 6).getD 2 (0, 0)) := by
  apply of_certificate witness002
  · decide +kernel
  · decide +kernel

private noncomputable def witness003 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row009

private theorem row003 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 3 (0, 0)) ((rowsAt 6).getD 3 (0, 0)) := by
  apply of_certificate witness003
  · decide +kernel
  · decide +kernel

private noncomputable def witness004 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row005

private theorem row004 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 4 (0, 0)) ((rowsAt 6).getD 4 (0, 0)) := by
  apply of_certificate witness004
  · decide +kernel
  · decide +kernel

private noncomputable def witness005 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row012

private theorem row005 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 5 (0, 0)) ((rowsAt 6).getD 5 (0, 0)) := by
  apply of_certificate witness005
  · decide +kernel
  · decide +kernel

private noncomputable def witness006 : Cert (n := 896) (rowsAt 5) :=
  (add Basis05.row001 node00796)

private theorem row006 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 6 (0, 0)) ((rowsAt 6).getD 6 (0, 0)) := by
  apply of_certificate witness006
  · decide +kernel
  · decide +kernel

private noncomputable def witness007 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row015

private theorem row007 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 7 (0, 0)) ((rowsAt 6).getD 7 (0, 0)) := by
  apply of_certificate witness007
  · decide +kernel
  · decide +kernel

private noncomputable def witness008 : Cert (n := 896) (rowsAt 5) :=
  (add Basis05.row000 (add Basis05.row001 Basis05.row005))

private theorem row008 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 8 (0, 0)) ((rowsAt 6).getD 8 (0, 0)) := by
  apply of_certificate witness008
  · decide +kernel
  · decide +kernel

private noncomputable def witness009 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row020

private theorem row009 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 9 (0, 0)) ((rowsAt 6).getD 9 (0, 0)) := by
  apply of_certificate witness009
  · decide +kernel
  · decide +kernel

private noncomputable def witness010 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row011

private theorem row010 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 10 (0, 0)) ((rowsAt 6).getD 10 (0, 0)) := by
  apply of_certificate witness010
  · decide +kernel
  · decide +kernel

private noncomputable def witness011 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row025

private theorem row011 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 11 (0, 0)) ((rowsAt 6).getD 11 (0, 0)) := by
  apply of_certificate witness011
  · decide +kernel
  · decide +kernel

private noncomputable def witness012 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row028

private theorem row012 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 12 (0, 0)) ((rowsAt 6).getD 12 (0, 0)) := by
  apply of_certificate witness012
  · decide +kernel
  · decide +kernel

private noncomputable def witness013 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row014

private theorem row013 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 13 (0, 0)) ((rowsAt 6).getD 13 (0, 0)) := by
  apply of_certificate witness013
  · decide +kernel
  · decide +kernel

private noncomputable def witness014 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row033

private theorem row014 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 14 (0, 0)) ((rowsAt 6).getD 14 (0, 0)) := by
  apply of_certificate witness014
  · decide +kernel
  · decide +kernel

private noncomputable def witness015 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row036

private theorem row015 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 15 (0, 0)) ((rowsAt 6).getD 15 (0, 0)) := by
  apply of_certificate witness015
  · decide +kernel
  · decide +kernel

private noncomputable def witness016 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row017

private theorem row016 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 16 (0, 0)) ((rowsAt 6).getD 16 (0, 0)) := by
  apply of_certificate witness016
  · decide +kernel
  · decide +kernel

private noncomputable def witness017 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row041

private theorem row017 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 17 (0, 0)) ((rowsAt 6).getD 17 (0, 0)) := by
  apply of_certificate witness017
  · decide +kernel
  · decide +kernel

private noncomputable def witness018 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row019

private theorem row018 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 18 (0, 0)) ((rowsAt 6).getD 18 (0, 0)) := by
  apply of_certificate witness018
  · decide +kernel
  · decide +kernel

private noncomputable def witness019 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row045

private theorem row019 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 19 (0, 0)) ((rowsAt 6).getD 19 (0, 0)) := by
  apply of_certificate witness019
  · decide +kernel
  · decide +kernel

private noncomputable def witness020 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row048

private theorem row020 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 20 (0, 0)) ((rowsAt 6).getD 20 (0, 0)) := by
  apply of_certificate witness020
  · decide +kernel
  · decide +kernel

private noncomputable def witness021 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row022

private theorem row021 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 21 (0, 0)) ((rowsAt 6).getD 21 (0, 0)) := by
  apply of_certificate witness021
  · decide +kernel
  · decide +kernel

private noncomputable def witness022 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row053

private theorem row022 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 22 (0, 0)) ((rowsAt 6).getD 22 (0, 0)) := by
  apply of_certificate witness022
  · decide +kernel
  · decide +kernel

private noncomputable def witness023 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row024

private theorem row023 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 23 (0, 0)) ((rowsAt 6).getD 23 (0, 0)) := by
  apply of_certificate witness023
  · decide +kernel
  · decide +kernel

private noncomputable def witness024 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row057

private theorem row024 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 24 (0, 0)) ((rowsAt 6).getD 24 (0, 0)) := by
  apply of_certificate witness024
  · decide +kernel
  · decide +kernel

private noncomputable def witness025 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row060

private theorem row025 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 25 (0, 0)) ((rowsAt 6).getD 25 (0, 0)) := by
  apply of_certificate witness025
  · decide +kernel
  · decide +kernel

private noncomputable def witness026 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row027

private theorem row026 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 26 (0, 0)) ((rowsAt 6).getD 26 (0, 0)) := by
  apply of_certificate witness026
  · decide +kernel
  · decide +kernel

private noncomputable def witness027 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row065

private theorem row027 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 27 (0, 0)) ((rowsAt 6).getD 27 (0, 0)) := by
  apply of_certificate witness027
  · decide +kernel
  · decide +kernel

private noncomputable def witness028 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row066

private theorem row028 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 28 (0, 0)) ((rowsAt 6).getD 28 (0, 0)) := by
  apply of_certificate witness028
  · decide +kernel
  · decide +kernel

private noncomputable def witness029 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row030

private theorem row029 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 29 (0, 0)) ((rowsAt 6).getD 29 (0, 0)) := by
  apply of_certificate witness029
  · decide +kernel
  · decide +kernel

private noncomputable def witness030 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row071

private theorem row030 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 30 (0, 0)) ((rowsAt 6).getD 30 (0, 0)) := by
  apply of_certificate witness030
  · decide +kernel
  · decide +kernel

private noncomputable def witness031 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row032

private theorem row031 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 31 (0, 0)) ((rowsAt 6).getD 31 (0, 0)) := by
  apply of_certificate witness031
  · decide +kernel
  · decide +kernel

private noncomputable def witness032 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row075

private theorem row032 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 32 (0, 0)) ((rowsAt 6).getD 32 (0, 0)) := by
  apply of_certificate witness032
  · decide +kernel
  · decide +kernel

private noncomputable def witness033 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row078

private theorem row033 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 33 (0, 0)) ((rowsAt 6).getD 33 (0, 0)) := by
  apply of_certificate witness033
  · decide +kernel
  · decide +kernel

private noncomputable def witness034 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row035

private theorem row034 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 34 (0, 0)) ((rowsAt 6).getD 34 (0, 0)) := by
  apply of_certificate witness034
  · decide +kernel
  · decide +kernel

private noncomputable def witness035 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row083

private theorem row035 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 35 (0, 0)) ((rowsAt 6).getD 35 (0, 0)) := by
  apply of_certificate witness035
  · decide +kernel
  · decide +kernel

private noncomputable def witness036 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row084

private theorem row036 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 36 (0, 0)) ((rowsAt 6).getD 36 (0, 0)) := by
  apply of_certificate witness036
  · decide +kernel
  · decide +kernel

private noncomputable def witness037 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row038

private theorem row037 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 37 (0, 0)) ((rowsAt 6).getD 37 (0, 0)) := by
  apply of_certificate witness037
  · decide +kernel
  · decide +kernel

private noncomputable def witness038 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row089

private theorem row038 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 38 (0, 0)) ((rowsAt 6).getD 38 (0, 0)) := by
  apply of_certificate witness038
  · decide +kernel
  · decide +kernel

private noncomputable def witness039 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row040

private theorem row039 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 39 (0, 0)) ((rowsAt 6).getD 39 (0, 0)) := by
  apply of_certificate witness039
  · decide +kernel
  · decide +kernel

private noncomputable def witness040 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row093

private theorem row040 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 40 (0, 0)) ((rowsAt 6).getD 40 (0, 0)) := by
  apply of_certificate witness040
  · decide +kernel
  · decide +kernel

private noncomputable def witness041 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row096

private theorem row041 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 41 (0, 0)) ((rowsAt 6).getD 41 (0, 0)) := by
  apply of_certificate witness041
  · decide +kernel
  · decide +kernel

private noncomputable def witness042 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row004

private theorem row042 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 42 (0, 0)) ((rowsAt 6).getD 42 (0, 0)) := by
  apply of_certificate witness042
  · decide +kernel
  · decide +kernel

private noncomputable def witness043 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row044

private theorem row043 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 43 (0, 0)) ((rowsAt 6).getD 43 (0, 0)) := by
  apply of_certificate witness043
  · decide +kernel
  · decide +kernel

private noncomputable def witness044 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row103

private theorem row044 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 44 (0, 0)) ((rowsAt 6).getD 44 (0, 0)) := by
  apply of_certificate witness044
  · decide +kernel
  · decide +kernel

private noncomputable def witness045 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row106

private theorem row045 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 45 (0, 0)) ((rowsAt 6).getD 45 (0, 0)) := by
  apply of_certificate witness045
  · decide +kernel
  · decide +kernel

private noncomputable def witness046 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row047

private theorem row046 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 46 (0, 0)) ((rowsAt 6).getD 46 (0, 0)) := by
  apply of_certificate witness046
  · decide +kernel
  · decide +kernel

private noncomputable def witness047 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row111

private theorem row047 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 47 (0, 0)) ((rowsAt 6).getD 47 (0, 0)) := by
  apply of_certificate witness047
  · decide +kernel
  · decide +kernel

private noncomputable def witness048 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row112

private theorem row048 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 48 (0, 0)) ((rowsAt 6).getD 48 (0, 0)) := by
  apply of_certificate witness048
  · decide +kernel
  · decide +kernel

private noncomputable def witness049 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row050

private theorem row049 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 49 (0, 0)) ((rowsAt 6).getD 49 (0, 0)) := by
  apply of_certificate witness049
  · decide +kernel
  · decide +kernel

private noncomputable def witness050 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row117

private theorem row050 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 50 (0, 0)) ((rowsAt 6).getD 50 (0, 0)) := by
  apply of_certificate witness050
  · decide +kernel
  · decide +kernel

private noncomputable def witness051 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row052

private theorem row051 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 51 (0, 0)) ((rowsAt 6).getD 51 (0, 0)) := by
  apply of_certificate witness051
  · decide +kernel
  · decide +kernel

private noncomputable def witness052 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row121

private theorem row052 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 52 (0, 0)) ((rowsAt 6).getD 52 (0, 0)) := by
  apply of_certificate witness052
  · decide +kernel
  · decide +kernel

private noncomputable def witness053 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row124

private theorem row053 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 53 (0, 0)) ((rowsAt 6).getD 53 (0, 0)) := by
  apply of_certificate witness053
  · decide +kernel
  · decide +kernel

private noncomputable def witness054 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row006

private theorem row054 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 54 (0, 0)) ((rowsAt 6).getD 54 (0, 0)) := by
  apply of_certificate witness054
  · decide +kernel
  · decide +kernel

private noncomputable def witness055 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row056

private theorem row055 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 55 (0, 0)) ((rowsAt 6).getD 55 (0, 0)) := by
  apply of_certificate witness055
  · decide +kernel
  · decide +kernel

private noncomputable def witness056 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row131

private theorem row056 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 56 (0, 0)) ((rowsAt 6).getD 56 (0, 0)) := by
  apply of_certificate witness056
  · decide +kernel
  · decide +kernel

private noncomputable def witness057 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row134

private theorem row057 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 57 (0, 0)) ((rowsAt 6).getD 57 (0, 0)) := by
  apply of_certificate witness057
  · decide +kernel
  · decide +kernel

private noncomputable def witness058 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row059

private theorem row058 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 58 (0, 0)) ((rowsAt 6).getD 58 (0, 0)) := by
  apply of_certificate witness058
  · decide +kernel
  · decide +kernel

private noncomputable def witness059 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row139

private theorem row059 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 59 (0, 0)) ((rowsAt 6).getD 59 (0, 0)) := by
  apply of_certificate witness059
  · decide +kernel
  · decide +kernel

private noncomputable def witness060 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row140

private theorem row060 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 60 (0, 0)) ((rowsAt 6).getD 60 (0, 0)) := by
  apply of_certificate witness060
  · decide +kernel
  · decide +kernel

private noncomputable def witness061 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row062

private theorem row061 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 61 (0, 0)) ((rowsAt 6).getD 61 (0, 0)) := by
  apply of_certificate witness061
  · decide +kernel
  · decide +kernel

private noncomputable def witness062 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row145

private theorem row062 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 62 (0, 0)) ((rowsAt 6).getD 62 (0, 0)) := by
  apply of_certificate witness062
  · decide +kernel
  · decide +kernel

private noncomputable def witness063 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row064

private theorem row063 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 63 (0, 0)) ((rowsAt 6).getD 63 (0, 0)) := by
  apply of_certificate witness063
  · decide +kernel
  · decide +kernel

private noncomputable def witness064 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row149

private theorem row064 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 64 (0, 0)) ((rowsAt 6).getD 64 (0, 0)) := by
  apply of_certificate witness064
  · decide +kernel
  · decide +kernel

private noncomputable def witness065 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row152

private theorem row065 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 65 (0, 0)) ((rowsAt 6).getD 65 (0, 0)) := by
  apply of_certificate witness065
  · decide +kernel
  · decide +kernel

private noncomputable def witness066 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row155

private theorem row066 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 66 (0, 0)) ((rowsAt 6).getD 66 (0, 0)) := by
  apply of_certificate witness066
  · decide +kernel
  · decide +kernel

private noncomputable def witness067 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row068

private theorem row067 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 67 (0, 0)) ((rowsAt 6).getD 67 (0, 0)) := by
  apply of_certificate witness067
  · decide +kernel
  · decide +kernel

private noncomputable def witness068 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row160

private theorem row068 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 68 (0, 0)) ((rowsAt 6).getD 68 (0, 0)) := by
  apply of_certificate witness068
  · decide +kernel
  · decide +kernel

private noncomputable def witness069 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row070

private theorem row069 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 69 (0, 0)) ((rowsAt 6).getD 69 (0, 0)) := by
  apply of_certificate witness069
  · decide +kernel
  · decide +kernel

private noncomputable def witness070 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row164

private theorem row070 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 70 (0, 0)) ((rowsAt 6).getD 70 (0, 0)) := by
  apply of_certificate witness070
  · decide +kernel
  · decide +kernel

private noncomputable def witness071 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row167

private theorem row071 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 71 (0, 0)) ((rowsAt 6).getD 71 (0, 0)) := by
  apply of_certificate witness071
  · decide +kernel
  · decide +kernel

private noncomputable def witness072 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row008

private theorem row072 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 72 (0, 0)) ((rowsAt 6).getD 72 (0, 0)) := by
  apply of_certificate witness072
  · decide +kernel
  · decide +kernel

private noncomputable def witness073 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row074

private theorem row073 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 73 (0, 0)) ((rowsAt 6).getD 73 (0, 0)) := by
  apply of_certificate witness073
  · decide +kernel
  · decide +kernel

private noncomputable def witness074 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row174

private theorem row074 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 74 (0, 0)) ((rowsAt 6).getD 74 (0, 0)) := by
  apply of_certificate witness074
  · decide +kernel
  · decide +kernel

private noncomputable def witness075 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row177

private theorem row075 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 75 (0, 0)) ((rowsAt 6).getD 75 (0, 0)) := by
  apply of_certificate witness075
  · decide +kernel
  · decide +kernel

private noncomputable def witness076 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row077

private theorem row076 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 76 (0, 0)) ((rowsAt 6).getD 76 (0, 0)) := by
  apply of_certificate witness076
  · decide +kernel
  · decide +kernel

private noncomputable def witness077 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row182

private theorem row077 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 77 (0, 0)) ((rowsAt 6).getD 77 (0, 0)) := by
  apply of_certificate witness077
  · decide +kernel
  · decide +kernel

private noncomputable def witness078 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row183

private theorem row078 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 78 (0, 0)) ((rowsAt 6).getD 78 (0, 0)) := by
  apply of_certificate witness078
  · decide +kernel
  · decide +kernel

private noncomputable def witness079 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row080

private theorem row079 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 79 (0, 0)) ((rowsAt 6).getD 79 (0, 0)) := by
  apply of_certificate witness079
  · decide +kernel
  · decide +kernel

private noncomputable def witness080 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row188

private theorem row080 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 80 (0, 0)) ((rowsAt 6).getD 80 (0, 0)) := by
  apply of_certificate witness080
  · decide +kernel
  · decide +kernel

private noncomputable def witness081 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row082

private theorem row081 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 81 (0, 0)) ((rowsAt 6).getD 81 (0, 0)) := by
  apply of_certificate witness081
  · decide +kernel
  · decide +kernel

private noncomputable def witness082 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row192

private theorem row082 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 82 (0, 0)) ((rowsAt 6).getD 82 (0, 0)) := by
  apply of_certificate witness082
  · decide +kernel
  · decide +kernel

private noncomputable def witness083 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row195

private theorem row083 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 83 (0, 0)) ((rowsAt 6).getD 83 (0, 0)) := by
  apply of_certificate witness083
  · decide +kernel
  · decide +kernel

private noncomputable def witness084 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row198

private theorem row084 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 84 (0, 0)) ((rowsAt 6).getD 84 (0, 0)) := by
  apply of_certificate witness084
  · decide +kernel
  · decide +kernel

private noncomputable def witness085 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row086

private theorem row085 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 85 (0, 0)) ((rowsAt 6).getD 85 (0, 0)) := by
  apply of_certificate witness085
  · decide +kernel
  · decide +kernel

private noncomputable def witness086 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row203

private theorem row086 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 86 (0, 0)) ((rowsAt 6).getD 86 (0, 0)) := by
  apply of_certificate witness086
  · decide +kernel
  · decide +kernel

private noncomputable def witness087 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row088

private theorem row087 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 87 (0, 0)) ((rowsAt 6).getD 87 (0, 0)) := by
  apply of_certificate witness087
  · decide +kernel
  · decide +kernel

private noncomputable def witness088 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row207

private theorem row088 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 88 (0, 0)) ((rowsAt 6).getD 88 (0, 0)) := by
  apply of_certificate witness088
  · decide +kernel
  · decide +kernel

private noncomputable def witness089 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row210

private theorem row089 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 89 (0, 0)) ((rowsAt 6).getD 89 (0, 0)) := by
  apply of_certificate witness089
  · decide +kernel
  · decide +kernel

private noncomputable def witness090 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row010

private theorem row090 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 90 (0, 0)) ((rowsAt 6).getD 90 (0, 0)) := by
  apply of_certificate witness090
  · decide +kernel
  · decide +kernel

private noncomputable def witness091 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row092

private theorem row091 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 91 (0, 0)) ((rowsAt 6).getD 91 (0, 0)) := by
  apply of_certificate witness091
  · decide +kernel
  · decide +kernel

private noncomputable def witness092 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row217

private theorem row092 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 92 (0, 0)) ((rowsAt 6).getD 92 (0, 0)) := by
  apply of_certificate witness092
  · decide +kernel
  · decide +kernel

private noncomputable def witness093 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row220

private theorem row093 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 93 (0, 0)) ((rowsAt 6).getD 93 (0, 0)) := by
  apply of_certificate witness093
  · decide +kernel
  · decide +kernel

private noncomputable def witness094 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row095

private theorem row094 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 94 (0, 0)) ((rowsAt 6).getD 94 (0, 0)) := by
  apply of_certificate witness094
  · decide +kernel
  · decide +kernel

private noncomputable def witness095 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row225

private theorem row095 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 95 (0, 0)) ((rowsAt 6).getD 95 (0, 0)) := by
  apply of_certificate witness095
  · decide +kernel
  · decide +kernel

private noncomputable def witness096 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row226

private theorem row096 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 96 (0, 0)) ((rowsAt 6).getD 96 (0, 0)) := by
  apply of_certificate witness096
  · decide +kernel
  · decide +kernel

private noncomputable def witness097 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row098

private theorem row097 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 97 (0, 0)) ((rowsAt 6).getD 97 (0, 0)) := by
  apply of_certificate witness097
  · decide +kernel
  · decide +kernel

private noncomputable def witness098 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row231

private theorem row098 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 98 (0, 0)) ((rowsAt 6).getD 98 (0, 0)) := by
  apply of_certificate witness098
  · decide +kernel
  · decide +kernel

private noncomputable def witness099 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row100

private theorem row099 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 99 (0, 0)) ((rowsAt 6).getD 99 (0, 0)) := by
  apply of_certificate witness099
  · decide +kernel
  · decide +kernel

private noncomputable def witness100 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row235

private theorem row100 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 100 (0, 0)) ((rowsAt 6).getD 100 (0, 0)) := by
  apply of_certificate witness100
  · decide +kernel
  · decide +kernel

private noncomputable def witness101 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row102

private theorem row101 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 101 (0, 0)) ((rowsAt 6).getD 101 (0, 0)) := by
  apply of_certificate witness101
  · decide +kernel
  · decide +kernel

private noncomputable def witness102 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row240

private theorem row102 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 102 (0, 0)) ((rowsAt 6).getD 102 (0, 0)) := by
  apply of_certificate witness102
  · decide +kernel
  · decide +kernel

private noncomputable def witness103 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row243

private theorem row103 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 103 (0, 0)) ((rowsAt 6).getD 103 (0, 0)) := by
  apply of_certificate witness103
  · decide +kernel
  · decide +kernel

private noncomputable def witness104 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row105

private theorem row104 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 104 (0, 0)) ((rowsAt 6).getD 104 (0, 0)) := by
  apply of_certificate witness104
  · decide +kernel
  · decide +kernel

private noncomputable def witness105 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row248

private theorem row105 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 105 (0, 0)) ((rowsAt 6).getD 105 (0, 0)) := by
  apply of_certificate witness105
  · decide +kernel
  · decide +kernel

private noncomputable def witness106 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row249

private theorem row106 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 106 (0, 0)) ((rowsAt 6).getD 106 (0, 0)) := by
  apply of_certificate witness106
  · decide +kernel
  · decide +kernel

private noncomputable def witness107 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row108

private theorem row107 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 107 (0, 0)) ((rowsAt 6).getD 107 (0, 0)) := by
  apply of_certificate witness107
  · decide +kernel
  · decide +kernel

private noncomputable def witness108 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row254

private theorem row108 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 108 (0, 0)) ((rowsAt 6).getD 108 (0, 0)) := by
  apply of_certificate witness108
  · decide +kernel
  · decide +kernel

private noncomputable def witness109 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row110

private theorem row109 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 109 (0, 0)) ((rowsAt 6).getD 109 (0, 0)) := by
  apply of_certificate witness109
  · decide +kernel
  · decide +kernel

private noncomputable def witness110 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row258

private theorem row110 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 110 (0, 0)) ((rowsAt 6).getD 110 (0, 0)) := by
  apply of_certificate witness110
  · decide +kernel
  · decide +kernel

private noncomputable def witness111 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row261

private theorem row111 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 111 (0, 0)) ((rowsAt 6).getD 111 (0, 0)) := by
  apply of_certificate witness111
  · decide +kernel
  · decide +kernel

private noncomputable def witness112 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row264

private theorem row112 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 112 (0, 0)) ((rowsAt 6).getD 112 (0, 0)) := by
  apply of_certificate witness112
  · decide +kernel
  · decide +kernel

private noncomputable def witness113 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row114

private theorem row113 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 113 (0, 0)) ((rowsAt 6).getD 113 (0, 0)) := by
  apply of_certificate witness113
  · decide +kernel
  · decide +kernel

private noncomputable def witness114 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row269

private theorem row114 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 114 (0, 0)) ((rowsAt 6).getD 114 (0, 0)) := by
  apply of_certificate witness114
  · decide +kernel
  · decide +kernel

private noncomputable def witness115 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row116

private theorem row115 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 115 (0, 0)) ((rowsAt 6).getD 115 (0, 0)) := by
  apply of_certificate witness115
  · decide +kernel
  · decide +kernel

private noncomputable def witness116 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row273

private theorem row116 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 116 (0, 0)) ((rowsAt 6).getD 116 (0, 0)) := by
  apply of_certificate witness116
  · decide +kernel
  · decide +kernel

private noncomputable def witness117 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row276

private theorem row117 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 117 (0, 0)) ((rowsAt 6).getD 117 (0, 0)) := by
  apply of_certificate witness117
  · decide +kernel
  · decide +kernel

private noncomputable def witness118 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row013

private theorem row118 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 118 (0, 0)) ((rowsAt 6).getD 118 (0, 0)) := by
  apply of_certificate witness118
  · decide +kernel
  · decide +kernel

private noncomputable def witness119 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row120

private theorem row119 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 119 (0, 0)) ((rowsAt 6).getD 119 (0, 0)) := by
  apply of_certificate witness119
  · decide +kernel
  · decide +kernel

private noncomputable def witness120 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row283

private theorem row120 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 120 (0, 0)) ((rowsAt 6).getD 120 (0, 0)) := by
  apply of_certificate witness120
  · decide +kernel
  · decide +kernel

private noncomputable def witness121 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row286

private theorem row121 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 121 (0, 0)) ((rowsAt 6).getD 121 (0, 0)) := by
  apply of_certificate witness121
  · decide +kernel
  · decide +kernel

private noncomputable def witness122 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row123

private theorem row122 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 122 (0, 0)) ((rowsAt 6).getD 122 (0, 0)) := by
  apply of_certificate witness122
  · decide +kernel
  · decide +kernel

private noncomputable def witness123 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row291

private theorem row123 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 123 (0, 0)) ((rowsAt 6).getD 123 (0, 0)) := by
  apply of_certificate witness123
  · decide +kernel
  · decide +kernel

private noncomputable def witness124 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row292

private theorem row124 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 124 (0, 0)) ((rowsAt 6).getD 124 (0, 0)) := by
  apply of_certificate witness124
  · decide +kernel
  · decide +kernel

private noncomputable def witness125 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row126

private theorem row125 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 125 (0, 0)) ((rowsAt 6).getD 125 (0, 0)) := by
  apply of_certificate witness125
  · decide +kernel
  · decide +kernel

private noncomputable def witness126 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row297

private theorem row126 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 126 (0, 0)) ((rowsAt 6).getD 126 (0, 0)) := by
  apply of_certificate witness126
  · decide +kernel
  · decide +kernel

private noncomputable def witness127 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row128

private theorem row127 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 127 (0, 0)) ((rowsAt 6).getD 127 (0, 0)) := by
  apply of_certificate witness127
  · decide +kernel
  · decide +kernel

private noncomputable def witness128 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row301

private theorem row128 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 128 (0, 0)) ((rowsAt 6).getD 128 (0, 0)) := by
  apply of_certificate witness128
  · decide +kernel
  · decide +kernel

private noncomputable def witness129 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row130

private theorem row129 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 129 (0, 0)) ((rowsAt 6).getD 129 (0, 0)) := by
  apply of_certificate witness129
  · decide +kernel
  · decide +kernel

private noncomputable def witness130 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row306

private theorem row130 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 130 (0, 0)) ((rowsAt 6).getD 130 (0, 0)) := by
  apply of_certificate witness130
  · decide +kernel
  · decide +kernel

private noncomputable def witness131 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row309

private theorem row131 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 131 (0, 0)) ((rowsAt 6).getD 131 (0, 0)) := by
  apply of_certificate witness131
  · decide +kernel
  · decide +kernel

private noncomputable def witness132 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row133

private theorem row132 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 132 (0, 0)) ((rowsAt 6).getD 132 (0, 0)) := by
  apply of_certificate witness132
  · decide +kernel
  · decide +kernel

private noncomputable def witness133 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row314

private theorem row133 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 133 (0, 0)) ((rowsAt 6).getD 133 (0, 0)) := by
  apply of_certificate witness133
  · decide +kernel
  · decide +kernel

private noncomputable def witness134 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row315

private theorem row134 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 134 (0, 0)) ((rowsAt 6).getD 134 (0, 0)) := by
  apply of_certificate witness134
  · decide +kernel
  · decide +kernel

private noncomputable def witness135 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row136

private theorem row135 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 135 (0, 0)) ((rowsAt 6).getD 135 (0, 0)) := by
  apply of_certificate witness135
  · decide +kernel
  · decide +kernel

private noncomputable def witness136 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row320

private theorem row136 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 136 (0, 0)) ((rowsAt 6).getD 136 (0, 0)) := by
  apply of_certificate witness136
  · decide +kernel
  · decide +kernel

private noncomputable def witness137 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row138

private theorem row137 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 137 (0, 0)) ((rowsAt 6).getD 137 (0, 0)) := by
  apply of_certificate witness137
  · decide +kernel
  · decide +kernel

private noncomputable def witness138 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row324

private theorem row138 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 138 (0, 0)) ((rowsAt 6).getD 138 (0, 0)) := by
  apply of_certificate witness138
  · decide +kernel
  · decide +kernel

private noncomputable def witness139 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row327

private theorem row139 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 139 (0, 0)) ((rowsAt 6).getD 139 (0, 0)) := by
  apply of_certificate witness139
  · decide +kernel
  · decide +kernel

private noncomputable def witness140 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row330

private theorem row140 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 140 (0, 0)) ((rowsAt 6).getD 140 (0, 0)) := by
  apply of_certificate witness140
  · decide +kernel
  · decide +kernel

private noncomputable def witness141 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row142

private theorem row141 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 141 (0, 0)) ((rowsAt 6).getD 141 (0, 0)) := by
  apply of_certificate witness141
  · decide +kernel
  · decide +kernel

private noncomputable def witness142 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row335

private theorem row142 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 142 (0, 0)) ((rowsAt 6).getD 142 (0, 0)) := by
  apply of_certificate witness142
  · decide +kernel
  · decide +kernel

private noncomputable def witness143 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row144

private theorem row143 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 143 (0, 0)) ((rowsAt 6).getD 143 (0, 0)) := by
  apply of_certificate witness143
  · decide +kernel
  · decide +kernel

private noncomputable def witness144 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row339

private theorem row144 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 144 (0, 0)) ((rowsAt 6).getD 144 (0, 0)) := by
  apply of_certificate witness144
  · decide +kernel
  · decide +kernel

private noncomputable def witness145 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row342

private theorem row145 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 145 (0, 0)) ((rowsAt 6).getD 145 (0, 0)) := by
  apply of_certificate witness145
  · decide +kernel
  · decide +kernel

private noncomputable def witness146 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row016

private theorem row146 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 146 (0, 0)) ((rowsAt 6).getD 146 (0, 0)) := by
  apply of_certificate witness146
  · decide +kernel
  · decide +kernel

private noncomputable def witness147 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row148

private theorem row147 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 147 (0, 0)) ((rowsAt 6).getD 147 (0, 0)) := by
  apply of_certificate witness147
  · decide +kernel
  · decide +kernel

private noncomputable def witness148 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row349

private theorem row148 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 148 (0, 0)) ((rowsAt 6).getD 148 (0, 0)) := by
  apply of_certificate witness148
  · decide +kernel
  · decide +kernel

private noncomputable def witness149 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row352

private theorem row149 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 149 (0, 0)) ((rowsAt 6).getD 149 (0, 0)) := by
  apply of_certificate witness149
  · decide +kernel
  · decide +kernel

private noncomputable def witness150 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row151

private theorem row150 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 150 (0, 0)) ((rowsAt 6).getD 150 (0, 0)) := by
  apply of_certificate witness150
  · decide +kernel
  · decide +kernel

private noncomputable def witness151 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row357

private theorem row151 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 151 (0, 0)) ((rowsAt 6).getD 151 (0, 0)) := by
  apply of_certificate witness151
  · decide +kernel
  · decide +kernel

private noncomputable def witness152 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row358

private theorem row152 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 152 (0, 0)) ((rowsAt 6).getD 152 (0, 0)) := by
  apply of_certificate witness152
  · decide +kernel
  · decide +kernel

private noncomputable def witness153 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row154

private theorem row153 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 153 (0, 0)) ((rowsAt 6).getD 153 (0, 0)) := by
  apply of_certificate witness153
  · decide +kernel
  · decide +kernel

private noncomputable def witness154 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row363

private theorem row154 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 154 (0, 0)) ((rowsAt 6).getD 154 (0, 0)) := by
  apply of_certificate witness154
  · decide +kernel
  · decide +kernel

private noncomputable def witness155 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row365

private theorem row155 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 155 (0, 0)) ((rowsAt 6).getD 155 (0, 0)) := by
  apply of_certificate witness155
  · decide +kernel
  · decide +kernel

private noncomputable def witness156 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row157

private theorem row156 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 156 (0, 0)) ((rowsAt 6).getD 156 (0, 0)) := by
  apply of_certificate witness156
  · decide +kernel
  · decide +kernel

private noncomputable def witness157 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row370

private theorem row157 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 157 (0, 0)) ((rowsAt 6).getD 157 (0, 0)) := by
  apply of_certificate witness157
  · decide +kernel
  · decide +kernel

private noncomputable def witness158 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row159

private theorem row158 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 158 (0, 0)) ((rowsAt 6).getD 158 (0, 0)) := by
  apply of_certificate witness158
  · decide +kernel
  · decide +kernel

private noncomputable def witness159 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row374

private theorem row159 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 159 (0, 0)) ((rowsAt 6).getD 159 (0, 0)) := by
  apply of_certificate witness159
  · decide +kernel
  · decide +kernel

private noncomputable def witness160 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row377

private theorem row160 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 160 (0, 0)) ((rowsAt 6).getD 160 (0, 0)) := by
  apply of_certificate witness160
  · decide +kernel
  · decide +kernel

private noncomputable def witness161 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row018

private theorem row161 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 161 (0, 0)) ((rowsAt 6).getD 161 (0, 0)) := by
  apply of_certificate witness161
  · decide +kernel
  · decide +kernel

private noncomputable def witness162 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row163

private theorem row162 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 162 (0, 0)) ((rowsAt 6).getD 162 (0, 0)) := by
  apply of_certificate witness162
  · decide +kernel
  · decide +kernel

private noncomputable def witness163 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row384

private theorem row163 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 163 (0, 0)) ((rowsAt 6).getD 163 (0, 0)) := by
  apply of_certificate witness163
  · decide +kernel
  · decide +kernel

private noncomputable def witness164 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row387

private theorem row164 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 164 (0, 0)) ((rowsAt 6).getD 164 (0, 0)) := by
  apply of_certificate witness164
  · decide +kernel
  · decide +kernel

private noncomputable def witness165 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row166

private theorem row165 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 165 (0, 0)) ((rowsAt 6).getD 165 (0, 0)) := by
  apply of_certificate witness165
  · decide +kernel
  · decide +kernel

private noncomputable def witness166 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row392

private theorem row166 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 166 (0, 0)) ((rowsAt 6).getD 166 (0, 0)) := by
  apply of_certificate witness166
  · decide +kernel
  · decide +kernel

private noncomputable def witness167 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row393

private theorem row167 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 167 (0, 0)) ((rowsAt 6).getD 167 (0, 0)) := by
  apply of_certificate witness167
  · decide +kernel
  · decide +kernel

private noncomputable def witness168 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row169

private theorem row168 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 168 (0, 0)) ((rowsAt 6).getD 168 (0, 0)) := by
  apply of_certificate witness168
  · decide +kernel
  · decide +kernel

private noncomputable def witness169 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row398

private theorem row169 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 169 (0, 0)) ((rowsAt 6).getD 169 (0, 0)) := by
  apply of_certificate witness169
  · decide +kernel
  · decide +kernel

private noncomputable def witness170 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row171

private theorem row170 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 170 (0, 0)) ((rowsAt 6).getD 170 (0, 0)) := by
  apply of_certificate witness170
  · decide +kernel
  · decide +kernel

private noncomputable def witness171 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row402

private theorem row171 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 171 (0, 0)) ((rowsAt 6).getD 171 (0, 0)) := by
  apply of_certificate witness171
  · decide +kernel
  · decide +kernel

private noncomputable def witness172 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row173

private theorem row172 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 172 (0, 0)) ((rowsAt 6).getD 172 (0, 0)) := by
  apply of_certificate witness172
  · decide +kernel
  · decide +kernel

private noncomputable def witness173 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row407

private theorem row173 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 173 (0, 0)) ((rowsAt 6).getD 173 (0, 0)) := by
  apply of_certificate witness173
  · decide +kernel
  · decide +kernel

private noncomputable def witness174 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row410

private theorem row174 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 174 (0, 0)) ((rowsAt 6).getD 174 (0, 0)) := by
  apply of_certificate witness174
  · decide +kernel
  · decide +kernel

private noncomputable def witness175 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row176

private theorem row175 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 175 (0, 0)) ((rowsAt 6).getD 175 (0, 0)) := by
  apply of_certificate witness175
  · decide +kernel
  · decide +kernel

private noncomputable def witness176 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row415

private theorem row176 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 176 (0, 0)) ((rowsAt 6).getD 176 (0, 0)) := by
  apply of_certificate witness176
  · decide +kernel
  · decide +kernel

private noncomputable def witness177 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row416

private theorem row177 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 177 (0, 0)) ((rowsAt 6).getD 177 (0, 0)) := by
  apply of_certificate witness177
  · decide +kernel
  · decide +kernel

private noncomputable def witness178 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row179

private theorem row178 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 178 (0, 0)) ((rowsAt 6).getD 178 (0, 0)) := by
  apply of_certificate witness178
  · decide +kernel
  · decide +kernel

private noncomputable def witness179 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row421

private theorem row179 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 179 (0, 0)) ((rowsAt 6).getD 179 (0, 0)) := by
  apply of_certificate witness179
  · decide +kernel
  · decide +kernel

private noncomputable def witness180 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row181

private theorem row180 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 180 (0, 0)) ((rowsAt 6).getD 180 (0, 0)) := by
  apply of_certificate witness180
  · decide +kernel
  · decide +kernel

private noncomputable def witness181 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row425

private theorem row181 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 181 (0, 0)) ((rowsAt 6).getD 181 (0, 0)) := by
  apply of_certificate witness181
  · decide +kernel
  · decide +kernel

private noncomputable def witness182 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row428

private theorem row182 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 182 (0, 0)) ((rowsAt 6).getD 182 (0, 0)) := by
  apply of_certificate witness182
  · decide +kernel
  · decide +kernel

private noncomputable def witness183 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row431

private theorem row183 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 183 (0, 0)) ((rowsAt 6).getD 183 (0, 0)) := by
  apply of_certificate witness183
  · decide +kernel
  · decide +kernel

private noncomputable def witness184 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row185

private theorem row184 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 184 (0, 0)) ((rowsAt 6).getD 184 (0, 0)) := by
  apply of_certificate witness184
  · decide +kernel
  · decide +kernel

private noncomputable def witness185 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row436

private theorem row185 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 185 (0, 0)) ((rowsAt 6).getD 185 (0, 0)) := by
  apply of_certificate witness185
  · decide +kernel
  · decide +kernel

private noncomputable def witness186 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row187

private theorem row186 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 186 (0, 0)) ((rowsAt 6).getD 186 (0, 0)) := by
  apply of_certificate witness186
  · decide +kernel
  · decide +kernel

private noncomputable def witness187 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row440

private theorem row187 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 187 (0, 0)) ((rowsAt 6).getD 187 (0, 0)) := by
  apply of_certificate witness187
  · decide +kernel
  · decide +kernel

private noncomputable def witness188 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row443

private theorem row188 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 188 (0, 0)) ((rowsAt 6).getD 188 (0, 0)) := by
  apply of_certificate witness188
  · decide +kernel
  · decide +kernel

private noncomputable def witness189 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row021

private theorem row189 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 189 (0, 0)) ((rowsAt 6).getD 189 (0, 0)) := by
  apply of_certificate witness189
  · decide +kernel
  · decide +kernel

private noncomputable def witness190 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row191

private theorem row190 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 190 (0, 0)) ((rowsAt 6).getD 190 (0, 0)) := by
  apply of_certificate witness190
  · decide +kernel
  · decide +kernel

private noncomputable def witness191 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row450

private theorem row191 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 191 (0, 0)) ((rowsAt 6).getD 191 (0, 0)) := by
  apply of_certificate witness191
  · decide +kernel
  · decide +kernel

private noncomputable def witness192 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row453

private theorem row192 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 192 (0, 0)) ((rowsAt 6).getD 192 (0, 0)) := by
  apply of_certificate witness192
  · decide +kernel
  · decide +kernel

private noncomputable def witness193 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row194

private theorem row193 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 193 (0, 0)) ((rowsAt 6).getD 193 (0, 0)) := by
  apply of_certificate witness193
  · decide +kernel
  · decide +kernel

private noncomputable def witness194 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row458

private theorem row194 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 194 (0, 0)) ((rowsAt 6).getD 194 (0, 0)) := by
  apply of_certificate witness194
  · decide +kernel
  · decide +kernel

private noncomputable def witness195 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row459

private theorem row195 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 195 (0, 0)) ((rowsAt 6).getD 195 (0, 0)) := by
  apply of_certificate witness195
  · decide +kernel
  · decide +kernel

private noncomputable def witness196 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row197

private theorem row196 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 196 (0, 0)) ((rowsAt 6).getD 196 (0, 0)) := by
  apply of_certificate witness196
  · decide +kernel
  · decide +kernel

private noncomputable def witness197 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row464

private theorem row197 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 197 (0, 0)) ((rowsAt 6).getD 197 (0, 0)) := by
  apply of_certificate witness197
  · decide +kernel
  · decide +kernel

private noncomputable def witness198 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row466

private theorem row198 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 198 (0, 0)) ((rowsAt 6).getD 198 (0, 0)) := by
  apply of_certificate witness198
  · decide +kernel
  · decide +kernel

private noncomputable def witness199 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row200

private theorem row199 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 199 (0, 0)) ((rowsAt 6).getD 199 (0, 0)) := by
  apply of_certificate witness199
  · decide +kernel
  · decide +kernel

private noncomputable def witness200 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row471

private theorem row200 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 200 (0, 0)) ((rowsAt 6).getD 200 (0, 0)) := by
  apply of_certificate witness200
  · decide +kernel
  · decide +kernel

private noncomputable def witness201 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row202

private theorem row201 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 201 (0, 0)) ((rowsAt 6).getD 201 (0, 0)) := by
  apply of_certificate witness201
  · decide +kernel
  · decide +kernel

private noncomputable def witness202 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row475

private theorem row202 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 202 (0, 0)) ((rowsAt 6).getD 202 (0, 0)) := by
  apply of_certificate witness202
  · decide +kernel
  · decide +kernel

private noncomputable def witness203 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row478

private theorem row203 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 203 (0, 0)) ((rowsAt 6).getD 203 (0, 0)) := by
  apply of_certificate witness203
  · decide +kernel
  · decide +kernel

private noncomputable def witness204 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row023

private theorem row204 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 204 (0, 0)) ((rowsAt 6).getD 204 (0, 0)) := by
  apply of_certificate witness204
  · decide +kernel
  · decide +kernel

private noncomputable def witness205 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row206

private theorem row205 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 205 (0, 0)) ((rowsAt 6).getD 205 (0, 0)) := by
  apply of_certificate witness205
  · decide +kernel
  · decide +kernel

private noncomputable def witness206 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row485

private theorem row206 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 206 (0, 0)) ((rowsAt 6).getD 206 (0, 0)) := by
  apply of_certificate witness206
  · decide +kernel
  · decide +kernel

private noncomputable def witness207 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row488

private theorem row207 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 207 (0, 0)) ((rowsAt 6).getD 207 (0, 0)) := by
  apply of_certificate witness207
  · decide +kernel
  · decide +kernel

private noncomputable def witness208 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row209

private theorem row208 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 208 (0, 0)) ((rowsAt 6).getD 208 (0, 0)) := by
  apply of_certificate witness208
  · decide +kernel
  · decide +kernel

private noncomputable def witness209 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row493

private theorem row209 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 209 (0, 0)) ((rowsAt 6).getD 209 (0, 0)) := by
  apply of_certificate witness209
  · decide +kernel
  · decide +kernel

private noncomputable def witness210 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row494

private theorem row210 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 210 (0, 0)) ((rowsAt 6).getD 210 (0, 0)) := by
  apply of_certificate witness210
  · decide +kernel
  · decide +kernel

private noncomputable def witness211 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row212

private theorem row211 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 211 (0, 0)) ((rowsAt 6).getD 211 (0, 0)) := by
  apply of_certificate witness211
  · decide +kernel
  · decide +kernel

private noncomputable def witness212 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row499

private theorem row212 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 212 (0, 0)) ((rowsAt 6).getD 212 (0, 0)) := by
  apply of_certificate witness212
  · decide +kernel
  · decide +kernel

private noncomputable def witness213 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row214

private theorem row213 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 213 (0, 0)) ((rowsAt 6).getD 213 (0, 0)) := by
  apply of_certificate witness213
  · decide +kernel
  · decide +kernel

private noncomputable def witness214 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row503

private theorem row214 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 214 (0, 0)) ((rowsAt 6).getD 214 (0, 0)) := by
  apply of_certificate witness214
  · decide +kernel
  · decide +kernel

private noncomputable def witness215 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row216

private theorem row215 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 215 (0, 0)) ((rowsAt 6).getD 215 (0, 0)) := by
  apply of_certificate witness215
  · decide +kernel
  · decide +kernel

private noncomputable def witness216 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row508

private theorem row216 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 216 (0, 0)) ((rowsAt 6).getD 216 (0, 0)) := by
  apply of_certificate witness216
  · decide +kernel
  · decide +kernel

private noncomputable def witness217 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row511

private theorem row217 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 217 (0, 0)) ((rowsAt 6).getD 217 (0, 0)) := by
  apply of_certificate witness217
  · decide +kernel
  · decide +kernel

private noncomputable def witness218 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row219

private theorem row218 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 218 (0, 0)) ((rowsAt 6).getD 218 (0, 0)) := by
  apply of_certificate witness218
  · decide +kernel
  · decide +kernel

private noncomputable def witness219 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row516

private theorem row219 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 219 (0, 0)) ((rowsAt 6).getD 219 (0, 0)) := by
  apply of_certificate witness219
  · decide +kernel
  · decide +kernel

private noncomputable def witness220 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row517

private theorem row220 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 220 (0, 0)) ((rowsAt 6).getD 220 (0, 0)) := by
  apply of_certificate witness220
  · decide +kernel
  · decide +kernel

private noncomputable def witness221 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row222

private theorem row221 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 221 (0, 0)) ((rowsAt 6).getD 221 (0, 0)) := by
  apply of_certificate witness221
  · decide +kernel
  · decide +kernel

private noncomputable def witness222 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row522

private theorem row222 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 222 (0, 0)) ((rowsAt 6).getD 222 (0, 0)) := by
  apply of_certificate witness222
  · decide +kernel
  · decide +kernel

private noncomputable def witness223 : Cert (n := 896) (rowsAt 5) :=
  Basis05.row224

private theorem row223 : Good (n := 896) (rowsAt 5)
    ((rowsAt 4).getD 223 (0, 0)) ((rowsAt 6).getD 223 (0, 0)) := by
  apply of_certificate witness223
  · decide +kernel
  · decide +kernel

private theorem block00 (i : ℕ) (hl : 0 ≤ i) (hu : i < 28) :
    Good (n := 896) (rowsAt 5) ((rowsAt 4).getD i (0, 0)) ((rowsAt 6).getD i (0, 0)) := by
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row000
  · exact row001
  · exact row002
  · exact row003
  · exact row004
  · exact row005
  · exact row006
  · exact row007
  · exact row008
  · exact row009
  · exact row010
  · exact row011
  · exact row012
  · exact row013
  · exact row014
  · exact row015
  · exact row016
  · exact row017
  · exact row018
  · exact row019
  · exact row020
  · exact row021
  · exact row022
  · exact row023
  · exact row024
  · exact row025
  · exact row026
  · exact row027

private theorem block01 (i : ℕ) (hl : 28 ≤ i) (hu : i < 56) :
    Good (n := 896) (rowsAt 5) ((rowsAt 4).getD i (0, 0)) ((rowsAt 6).getD i (0, 0)) := by
  have h : i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row028
  · exact row029
  · exact row030
  · exact row031
  · exact row032
  · exact row033
  · exact row034
  · exact row035
  · exact row036
  · exact row037
  · exact row038
  · exact row039
  · exact row040
  · exact row041
  · exact row042
  · exact row043
  · exact row044
  · exact row045
  · exact row046
  · exact row047
  · exact row048
  · exact row049
  · exact row050
  · exact row051
  · exact row052
  · exact row053
  · exact row054
  · exact row055

private theorem block02 (i : ℕ) (hl : 56 ≤ i) (hu : i < 84) :
    Good (n := 896) (rowsAt 5) ((rowsAt 4).getD i (0, 0)) ((rowsAt 6).getD i (0, 0)) := by
  have h : i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨ i = 61 ∨ i = 62 ∨ i = 63 ∨ i = 64 ∨ i = 65 ∨ i = 66 ∨ i = 67 ∨ i = 68 ∨ i = 69 ∨ i = 70 ∨ i = 71 ∨ i = 72 ∨ i = 73 ∨ i = 74 ∨ i = 75 ∨ i = 76 ∨ i = 77 ∨ i = 78 ∨ i = 79 ∨ i = 80 ∨ i = 81 ∨ i = 82 ∨ i = 83 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row056
  · exact row057
  · exact row058
  · exact row059
  · exact row060
  · exact row061
  · exact row062
  · exact row063
  · exact row064
  · exact row065
  · exact row066
  · exact row067
  · exact row068
  · exact row069
  · exact row070
  · exact row071
  · exact row072
  · exact row073
  · exact row074
  · exact row075
  · exact row076
  · exact row077
  · exact row078
  · exact row079
  · exact row080
  · exact row081
  · exact row082
  · exact row083

private theorem block03 (i : ℕ) (hl : 84 ≤ i) (hu : i < 112) :
    Good (n := 896) (rowsAt 5) ((rowsAt 4).getD i (0, 0)) ((rowsAt 6).getD i (0, 0)) := by
  have h : i = 84 ∨ i = 85 ∨ i = 86 ∨ i = 87 ∨ i = 88 ∨ i = 89 ∨ i = 90 ∨ i = 91 ∨ i = 92 ∨ i = 93 ∨ i = 94 ∨ i = 95 ∨ i = 96 ∨ i = 97 ∨ i = 98 ∨ i = 99 ∨ i = 100 ∨ i = 101 ∨ i = 102 ∨ i = 103 ∨ i = 104 ∨ i = 105 ∨ i = 106 ∨ i = 107 ∨ i = 108 ∨ i = 109 ∨ i = 110 ∨ i = 111 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row084
  · exact row085
  · exact row086
  · exact row087
  · exact row088
  · exact row089
  · exact row090
  · exact row091
  · exact row092
  · exact row093
  · exact row094
  · exact row095
  · exact row096
  · exact row097
  · exact row098
  · exact row099
  · exact row100
  · exact row101
  · exact row102
  · exact row103
  · exact row104
  · exact row105
  · exact row106
  · exact row107
  · exact row108
  · exact row109
  · exact row110
  · exact row111

private theorem block04 (i : ℕ) (hl : 112 ≤ i) (hu : i < 140) :
    Good (n := 896) (rowsAt 5) ((rowsAt 4).getD i (0, 0)) ((rowsAt 6).getD i (0, 0)) := by
  have h : i = 112 ∨ i = 113 ∨ i = 114 ∨ i = 115 ∨ i = 116 ∨ i = 117 ∨ i = 118 ∨ i = 119 ∨ i = 120 ∨ i = 121 ∨ i = 122 ∨ i = 123 ∨ i = 124 ∨ i = 125 ∨ i = 126 ∨ i = 127 ∨ i = 128 ∨ i = 129 ∨ i = 130 ∨ i = 131 ∨ i = 132 ∨ i = 133 ∨ i = 134 ∨ i = 135 ∨ i = 136 ∨ i = 137 ∨ i = 138 ∨ i = 139 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row112
  · exact row113
  · exact row114
  · exact row115
  · exact row116
  · exact row117
  · exact row118
  · exact row119
  · exact row120
  · exact row121
  · exact row122
  · exact row123
  · exact row124
  · exact row125
  · exact row126
  · exact row127
  · exact row128
  · exact row129
  · exact row130
  · exact row131
  · exact row132
  · exact row133
  · exact row134
  · exact row135
  · exact row136
  · exact row137
  · exact row138
  · exact row139

private theorem block05 (i : ℕ) (hl : 140 ≤ i) (hu : i < 168) :
    Good (n := 896) (rowsAt 5) ((rowsAt 4).getD i (0, 0)) ((rowsAt 6).getD i (0, 0)) := by
  have h : i = 140 ∨ i = 141 ∨ i = 142 ∨ i = 143 ∨ i = 144 ∨ i = 145 ∨ i = 146 ∨ i = 147 ∨ i = 148 ∨ i = 149 ∨ i = 150 ∨ i = 151 ∨ i = 152 ∨ i = 153 ∨ i = 154 ∨ i = 155 ∨ i = 156 ∨ i = 157 ∨ i = 158 ∨ i = 159 ∨ i = 160 ∨ i = 161 ∨ i = 162 ∨ i = 163 ∨ i = 164 ∨ i = 165 ∨ i = 166 ∨ i = 167 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row140
  · exact row141
  · exact row142
  · exact row143
  · exact row144
  · exact row145
  · exact row146
  · exact row147
  · exact row148
  · exact row149
  · exact row150
  · exact row151
  · exact row152
  · exact row153
  · exact row154
  · exact row155
  · exact row156
  · exact row157
  · exact row158
  · exact row159
  · exact row160
  · exact row161
  · exact row162
  · exact row163
  · exact row164
  · exact row165
  · exact row166
  · exact row167

private theorem block06 (i : ℕ) (hl : 168 ≤ i) (hu : i < 196) :
    Good (n := 896) (rowsAt 5) ((rowsAt 4).getD i (0, 0)) ((rowsAt 6).getD i (0, 0)) := by
  have h : i = 168 ∨ i = 169 ∨ i = 170 ∨ i = 171 ∨ i = 172 ∨ i = 173 ∨ i = 174 ∨ i = 175 ∨ i = 176 ∨ i = 177 ∨ i = 178 ∨ i = 179 ∨ i = 180 ∨ i = 181 ∨ i = 182 ∨ i = 183 ∨ i = 184 ∨ i = 185 ∨ i = 186 ∨ i = 187 ∨ i = 188 ∨ i = 189 ∨ i = 190 ∨ i = 191 ∨ i = 192 ∨ i = 193 ∨ i = 194 ∨ i = 195 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row168
  · exact row169
  · exact row170
  · exact row171
  · exact row172
  · exact row173
  · exact row174
  · exact row175
  · exact row176
  · exact row177
  · exact row178
  · exact row179
  · exact row180
  · exact row181
  · exact row182
  · exact row183
  · exact row184
  · exact row185
  · exact row186
  · exact row187
  · exact row188
  · exact row189
  · exact row190
  · exact row191
  · exact row192
  · exact row193
  · exact row194
  · exact row195

private theorem block07 (i : ℕ) (hl : 196 ≤ i) (hu : i < 224) :
    Good (n := 896) (rowsAt 5) ((rowsAt 4).getD i (0, 0)) ((rowsAt 6).getD i (0, 0)) := by
  have h : i = 196 ∨ i = 197 ∨ i = 198 ∨ i = 199 ∨ i = 200 ∨ i = 201 ∨ i = 202 ∨ i = 203 ∨ i = 204 ∨ i = 205 ∨ i = 206 ∨ i = 207 ∨ i = 208 ∨ i = 209 ∨ i = 210 ∨ i = 211 ∨ i = 212 ∨ i = 213 ∨ i = 214 ∨ i = 215 ∨ i = 216 ∨ i = 217 ∨ i = 218 ∨ i = 219 ∨ i = 220 ∨ i = 221 ∨ i = 222 ∨ i = 223 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row196
  · exact row197
  · exact row198
  · exact row199
  · exact row200
  · exact row201
  · exact row202
  · exact row203
  · exact row204
  · exact row205
  · exact row206
  · exact row207
  · exact row208
  · exact row209
  · exact row210
  · exact row211
  · exact row212
  · exact row213
  · exact row214
  · exact row215
  · exact row216
  · exact row217
  · exact row218
  · exact row219
  · exact row220
  · exact row221
  · exact row222
  · exact row223

/-- Checked rows 0 through 223 of the literal fixed product. -/
theorem part00 (i : ℕ) (hl : 0 ≤ i) (hu : i < 224) :
    Good (n := 896) (rowsAt 5) ((rowsAt 4).getD i (0, 0)) ((rowsAt 6).getD i (0, 0)) := by
  have h : (0 ≤ i ∧ i < 28) ∨ (28 ≤ i ∧ i < 56) ∨ (56 ≤ i ∧ i < 84) ∨ (84 ≤ i ∧ i < 112) ∨ (112 ≤ i ∧ i < 140) ∨ (140 ≤ i ∧ i < 168) ∨ (168 ≤ i ∧ i < 196) ∨ (196 ≤ i ∧ i < 224) := by omega
  rcases h with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · exact block00 i h0.1 h0.2
  · exact block01 i h1.1 h1.2
  · exact block02 i h2.1 h2.2
  · exact block03 i h3.1 h3.2
  · exact block04 i h4.1 h4.2
  · exact block05 i h5.1 h5.2
  · exact block06 i h6.1 h6.2
  · exact block07 i h7.1 h7.2

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Shared.Mixed.Gate04
