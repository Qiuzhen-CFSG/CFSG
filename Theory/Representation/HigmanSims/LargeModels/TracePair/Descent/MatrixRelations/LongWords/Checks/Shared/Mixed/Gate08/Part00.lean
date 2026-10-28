module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.Shared.Mixed.Sums07

/-!
# Rows 0–223 of mixed product gate 8

Certificates for the literal HSG1-f4r896aB0 candidates. The generator
proposes witnesses only; all arithmetic equalities are checked by the kernel.
Source attribution and conventions: `TracePair/source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Shared.Mixed.Gate08
open Representation.HigmanSims.LargeModels.TracePair.Certificates
open Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.LinearCertificates

open Sums07

private noncomputable def witness000 : Cert (n := 896) (rowsAt 7) :=
  (add Basis07.row001 (add Basis07.row002 Basis07.row005))

private theorem row000 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 0 (0, 0)) ((rowsAt 10).getD 0 (0, 0)) := by
  apply of_certificate witness000
  · decide +kernel
  · decide +kernel

private noncomputable def witness001 : Cert (n := 896) (rowsAt 7) :=
  (add node00790 Basis07.row005)

private theorem row001 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 1 (0, 0)) ((rowsAt 10).getD 1 (0, 0)) := by
  apply of_certificate witness001
  · decide +kernel
  · decide +kernel

private noncomputable def witness002 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row017

private theorem row002 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 2 (0, 0)) ((rowsAt 10).getD 2 (0, 0)) := by
  apply of_certificate witness002
  · decide +kernel
  · decide +kernel

private noncomputable def witness003 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row022

private theorem row003 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 3 (0, 0)) ((rowsAt 10).getD 3 (0, 0)) := by
  apply of_certificate witness003
  · decide +kernel
  · decide +kernel

private noncomputable def witness004 : Cert (n := 896) (rowsAt 7) :=
  (add (add node00790 Basis07.row002) (add Basis07.row003 Basis07.row005))

private theorem row004 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 4 (0, 0)) ((rowsAt 10).getD 4 (0, 0)) := by
  apply of_certificate witness004
  · decide +kernel
  · decide +kernel

private noncomputable def witness005 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row030

private theorem row005 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 5 (0, 0)) ((rowsAt 10).getD 5 (0, 0)) := by
  apply of_certificate witness005
  · decide +kernel
  · decide +kernel

private noncomputable def witness006 : Cert (n := 896) (rowsAt 7) :=
  (add node00790 Basis07.row003)

private theorem row006 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 6 (0, 0)) ((rowsAt 10).getD 6 (0, 0)) := by
  apply of_certificate witness006
  · decide +kernel
  · decide +kernel

private noncomputable def witness007 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row038

private theorem row007 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 7 (0, 0)) ((rowsAt 10).getD 7 (0, 0)) := by
  apply of_certificate witness007
  · decide +kernel
  · decide +kernel

private noncomputable def witness008 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row000

private theorem row008 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 8 (0, 0)) ((rowsAt 10).getD 8 (0, 0)) := by
  apply of_certificate witness008
  · decide +kernel
  · decide +kernel

private noncomputable def witness009 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row050

private theorem row009 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 9 (0, 0)) ((rowsAt 10).getD 9 (0, 0)) := by
  apply of_certificate witness009
  · decide +kernel
  · decide +kernel

private noncomputable def witness010 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row027

private theorem row010 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 10 (0, 0)) ((rowsAt 10).getD 10 (0, 0)) := by
  apply of_certificate witness010
  · decide +kernel
  · decide +kernel

private noncomputable def witness011 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row062

private theorem row011 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 11 (0, 0)) ((rowsAt 10).getD 11 (0, 0)) := by
  apply of_certificate witness011
  · decide +kernel
  · decide +kernel

private noncomputable def witness012 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row068

private theorem row012 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 12 (0, 0)) ((rowsAt 10).getD 12 (0, 0)) := by
  apply of_certificate witness012
  · decide +kernel
  · decide +kernel

private noncomputable def witness013 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row035

private theorem row013 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 13 (0, 0)) ((rowsAt 10).getD 13 (0, 0)) := by
  apply of_certificate witness013
  · decide +kernel
  · decide +kernel

private noncomputable def witness014 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row080

private theorem row014 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 14 (0, 0)) ((rowsAt 10).getD 14 (0, 0)) := by
  apply of_certificate witness014
  · decide +kernel
  · decide +kernel

private noncomputable def witness015 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row086

private theorem row015 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 15 (0, 0)) ((rowsAt 10).getD 15 (0, 0)) := by
  apply of_certificate witness015
  · decide +kernel
  · decide +kernel

private noncomputable def witness016 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row004

private theorem row016 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 16 (0, 0)) ((rowsAt 10).getD 16 (0, 0)) := by
  apply of_certificate witness016
  · decide +kernel
  · decide +kernel

private noncomputable def witness017 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row098

private theorem row017 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 17 (0, 0)) ((rowsAt 10).getD 17 (0, 0)) := by
  apply of_certificate witness017
  · decide +kernel
  · decide +kernel

private noncomputable def witness018 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row047

private theorem row018 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 18 (0, 0)) ((rowsAt 10).getD 18 (0, 0)) := by
  apply of_certificate witness018
  · decide +kernel
  · decide +kernel

private noncomputable def witness019 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row108

private theorem row019 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 19 (0, 0)) ((rowsAt 10).getD 19 (0, 0)) := by
  apply of_certificate witness019
  · decide +kernel
  · decide +kernel

private noncomputable def witness020 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row114

private theorem row020 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 20 (0, 0)) ((rowsAt 10).getD 20 (0, 0)) := by
  apply of_certificate witness020
  · decide +kernel
  · decide +kernel

private noncomputable def witness021 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row006

private theorem row021 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 21 (0, 0)) ((rowsAt 10).getD 21 (0, 0)) := by
  apply of_certificate witness021
  · decide +kernel
  · decide +kernel

private noncomputable def witness022 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row126

private theorem row022 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 22 (0, 0)) ((rowsAt 10).getD 22 (0, 0)) := by
  apply of_certificate witness022
  · decide +kernel
  · decide +kernel

private noncomputable def witness023 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row059

private theorem row023 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 23 (0, 0)) ((rowsAt 10).getD 23 (0, 0)) := by
  apply of_certificate witness023
  · decide +kernel
  · decide +kernel

private noncomputable def witness024 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row136

private theorem row024 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 24 (0, 0)) ((rowsAt 10).getD 24 (0, 0)) := by
  apply of_certificate witness024
  · decide +kernel
  · decide +kernel

private noncomputable def witness025 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row142

private theorem row025 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 25 (0, 0)) ((rowsAt 10).getD 25 (0, 0)) := by
  apply of_certificate witness025
  · decide +kernel
  · decide +kernel

private noncomputable def witness026 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row007

private theorem row026 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 26 (0, 0)) ((rowsAt 10).getD 26 (0, 0)) := by
  apply of_certificate witness026
  · decide +kernel
  · decide +kernel

private noncomputable def witness027 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row154

private theorem row027 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 27 (0, 0)) ((rowsAt 10).getD 27 (0, 0)) := by
  apply of_certificate witness027
  · decide +kernel
  · decide +kernel

private noncomputable def witness028 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row157

private theorem row028 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 28 (0, 0)) ((rowsAt 10).getD 28 (0, 0)) := by
  apply of_certificate witness028
  · decide +kernel
  · decide +kernel

private noncomputable def witness029 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row008

private theorem row029 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 29 (0, 0)) ((rowsAt 10).getD 29 (0, 0)) := by
  apply of_certificate witness029
  · decide +kernel
  · decide +kernel

private noncomputable def witness030 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row169

private theorem row030 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 30 (0, 0)) ((rowsAt 10).getD 30 (0, 0)) := by
  apply of_certificate witness030
  · decide +kernel
  · decide +kernel

private noncomputable def witness031 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row077

private theorem row031 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 31 (0, 0)) ((rowsAt 10).getD 31 (0, 0)) := by
  apply of_certificate witness031
  · decide +kernel
  · decide +kernel

private noncomputable def witness032 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row179

private theorem row032 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 32 (0, 0)) ((rowsAt 10).getD 32 (0, 0)) := by
  apply of_certificate witness032
  · decide +kernel
  · decide +kernel

private noncomputable def witness033 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row185

private theorem row033 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 33 (0, 0)) ((rowsAt 10).getD 33 (0, 0)) := by
  apply of_certificate witness033
  · decide +kernel
  · decide +kernel

private noncomputable def witness034 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row009

private theorem row034 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 34 (0, 0)) ((rowsAt 10).getD 34 (0, 0)) := by
  apply of_certificate witness034
  · decide +kernel
  · decide +kernel

private noncomputable def witness035 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row197

private theorem row035 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 35 (0, 0)) ((rowsAt 10).getD 35 (0, 0)) := by
  apply of_certificate witness035
  · decide +kernel
  · decide +kernel

private noncomputable def witness036 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row200

private theorem row036 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 36 (0, 0)) ((rowsAt 10).getD 36 (0, 0)) := by
  apply of_certificate witness036
  · decide +kernel
  · decide +kernel

private noncomputable def witness037 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row010

private theorem row037 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 37 (0, 0)) ((rowsAt 10).getD 37 (0, 0)) := by
  apply of_certificate witness037
  · decide +kernel
  · decide +kernel

private noncomputable def witness038 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row212

private theorem row038 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 38 (0, 0)) ((rowsAt 10).getD 38 (0, 0)) := by
  apply of_certificate witness038
  · decide +kernel
  · decide +kernel

private noncomputable def witness039 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row095

private theorem row039 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 39 (0, 0)) ((rowsAt 10).getD 39 (0, 0)) := by
  apply of_certificate witness039
  · decide +kernel
  · decide +kernel

private noncomputable def witness040 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row222

private theorem row040 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 40 (0, 0)) ((rowsAt 10).getD 40 (0, 0)) := by
  apply of_certificate witness040
  · decide +kernel
  · decide +kernel

private noncomputable def witness041 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row228

private theorem row041 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 41 (0, 0)) ((rowsAt 10).getD 41 (0, 0)) := by
  apply of_certificate witness041
  · decide +kernel
  · decide +kernel

private noncomputable def witness042 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row011

private theorem row042 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 42 (0, 0)) ((rowsAt 10).getD 42 (0, 0)) := by
  apply of_certificate witness042
  · decide +kernel
  · decide +kernel

private noncomputable def witness043 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row105

private theorem row043 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 43 (0, 0)) ((rowsAt 10).getD 43 (0, 0)) := by
  apply of_certificate witness043
  · decide +kernel
  · decide +kernel

private noncomputable def witness044 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row245

private theorem row044 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 44 (0, 0)) ((rowsAt 10).getD 44 (0, 0)) := by
  apply of_certificate witness044
  · decide +kernel
  · decide +kernel

private noncomputable def witness045 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row251

private theorem row045 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 45 (0, 0)) ((rowsAt 10).getD 45 (0, 0)) := by
  apply of_certificate witness045
  · decide +kernel
  · decide +kernel

private noncomputable def witness046 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row012

private theorem row046 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 46 (0, 0)) ((rowsAt 10).getD 46 (0, 0)) := by
  apply of_certificate witness046
  · decide +kernel
  · decide +kernel

private noncomputable def witness047 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row263

private theorem row047 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 47 (0, 0)) ((rowsAt 10).getD 47 (0, 0)) := by
  apply of_certificate witness047
  · decide +kernel
  · decide +kernel

private noncomputable def witness048 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row266

private theorem row048 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 48 (0, 0)) ((rowsAt 10).getD 48 (0, 0)) := by
  apply of_certificate witness048
  · decide +kernel
  · decide +kernel

private noncomputable def witness049 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row013

private theorem row049 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 49 (0, 0)) ((rowsAt 10).getD 49 (0, 0)) := by
  apply of_certificate witness049
  · decide +kernel
  · decide +kernel

private noncomputable def witness050 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row278

private theorem row050 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 50 (0, 0)) ((rowsAt 10).getD 50 (0, 0)) := by
  apply of_certificate witness050
  · decide +kernel
  · decide +kernel

private noncomputable def witness051 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row123

private theorem row051 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 51 (0, 0)) ((rowsAt 10).getD 51 (0, 0)) := by
  apply of_certificate witness051
  · decide +kernel
  · decide +kernel

private noncomputable def witness052 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row288

private theorem row052 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 52 (0, 0)) ((rowsAt 10).getD 52 (0, 0)) := by
  apply of_certificate witness052
  · decide +kernel
  · decide +kernel

private noncomputable def witness053 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row294

private theorem row053 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 53 (0, 0)) ((rowsAt 10).getD 53 (0, 0)) := by
  apply of_certificate witness053
  · decide +kernel
  · decide +kernel

private noncomputable def witness054 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row014

private theorem row054 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 54 (0, 0)) ((rowsAt 10).getD 54 (0, 0)) := by
  apply of_certificate witness054
  · decide +kernel
  · decide +kernel

private noncomputable def witness055 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row133

private theorem row055 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 55 (0, 0)) ((rowsAt 10).getD 55 (0, 0)) := by
  apply of_certificate witness055
  · decide +kernel
  · decide +kernel

private noncomputable def witness056 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row311

private theorem row056 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 56 (0, 0)) ((rowsAt 10).getD 56 (0, 0)) := by
  apply of_certificate witness056
  · decide +kernel
  · decide +kernel

private noncomputable def witness057 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row317

private theorem row057 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 57 (0, 0)) ((rowsAt 10).getD 57 (0, 0)) := by
  apply of_certificate witness057
  · decide +kernel
  · decide +kernel

private noncomputable def witness058 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row015

private theorem row058 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 58 (0, 0)) ((rowsAt 10).getD 58 (0, 0)) := by
  apply of_certificate witness058
  · decide +kernel
  · decide +kernel

private noncomputable def witness059 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row329

private theorem row059 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 59 (0, 0)) ((rowsAt 10).getD 59 (0, 0)) := by
  apply of_certificate witness059
  · decide +kernel
  · decide +kernel

private noncomputable def witness060 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row332

private theorem row060 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 60 (0, 0)) ((rowsAt 10).getD 60 (0, 0)) := by
  apply of_certificate witness060
  · decide +kernel
  · decide +kernel

private noncomputable def witness061 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row016

private theorem row061 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 61 (0, 0)) ((rowsAt 10).getD 61 (0, 0)) := by
  apply of_certificate witness061
  · decide +kernel
  · decide +kernel

private noncomputable def witness062 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row344

private theorem row062 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 62 (0, 0)) ((rowsAt 10).getD 62 (0, 0)) := by
  apply of_certificate witness062
  · decide +kernel
  · decide +kernel

private noncomputable def witness063 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row151

private theorem row063 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 63 (0, 0)) ((rowsAt 10).getD 63 (0, 0)) := by
  apply of_certificate witness063
  · decide +kernel
  · decide +kernel

private noncomputable def witness064 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row354

private theorem row064 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 64 (0, 0)) ((rowsAt 10).getD 64 (0, 0)) := by
  apply of_certificate witness064
  · decide +kernel
  · decide +kernel

private noncomputable def witness065 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row360

private theorem row065 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 65 (0, 0)) ((rowsAt 10).getD 65 (0, 0)) := by
  apply of_certificate witness065
  · decide +kernel
  · decide +kernel

private noncomputable def witness066 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row367

private theorem row066 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 66 (0, 0)) ((rowsAt 10).getD 66 (0, 0)) := by
  apply of_certificate witness066
  · decide +kernel
  · decide +kernel

private noncomputable def witness067 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row018

private theorem row067 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 67 (0, 0)) ((rowsAt 10).getD 67 (0, 0)) := by
  apply of_certificate witness067
  · decide +kernel
  · decide +kernel

private noncomputable def witness068 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row379

private theorem row068 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 68 (0, 0)) ((rowsAt 10).getD 68 (0, 0)) := by
  apply of_certificate witness068
  · decide +kernel
  · decide +kernel

private noncomputable def witness069 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row166

private theorem row069 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 69 (0, 0)) ((rowsAt 10).getD 69 (0, 0)) := by
  apply of_certificate witness069
  · decide +kernel
  · decide +kernel

private noncomputable def witness070 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row389

private theorem row070 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 70 (0, 0)) ((rowsAt 10).getD 70 (0, 0)) := by
  apply of_certificate witness070
  · decide +kernel
  · decide +kernel

private noncomputable def witness071 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row395

private theorem row071 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 71 (0, 0)) ((rowsAt 10).getD 71 (0, 0)) := by
  apply of_certificate witness071
  · decide +kernel
  · decide +kernel

private noncomputable def witness072 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row019

private theorem row072 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 72 (0, 0)) ((rowsAt 10).getD 72 (0, 0)) := by
  apply of_certificate witness072
  · decide +kernel
  · decide +kernel

private noncomputable def witness073 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row176

private theorem row073 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 73 (0, 0)) ((rowsAt 10).getD 73 (0, 0)) := by
  apply of_certificate witness073
  · decide +kernel
  · decide +kernel

private noncomputable def witness074 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row412

private theorem row074 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 74 (0, 0)) ((rowsAt 10).getD 74 (0, 0)) := by
  apply of_certificate witness074
  · decide +kernel
  · decide +kernel

private noncomputable def witness075 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row418

private theorem row075 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 75 (0, 0)) ((rowsAt 10).getD 75 (0, 0)) := by
  apply of_certificate witness075
  · decide +kernel
  · decide +kernel

private noncomputable def witness076 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row020

private theorem row076 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 76 (0, 0)) ((rowsAt 10).getD 76 (0, 0)) := by
  apply of_certificate witness076
  · decide +kernel
  · decide +kernel

private noncomputable def witness077 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row430

private theorem row077 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 77 (0, 0)) ((rowsAt 10).getD 77 (0, 0)) := by
  apply of_certificate witness077
  · decide +kernel
  · decide +kernel

private noncomputable def witness078 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row433

private theorem row078 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 78 (0, 0)) ((rowsAt 10).getD 78 (0, 0)) := by
  apply of_certificate witness078
  · decide +kernel
  · decide +kernel

private noncomputable def witness079 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row021

private theorem row079 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 79 (0, 0)) ((rowsAt 10).getD 79 (0, 0)) := by
  apply of_certificate witness079
  · decide +kernel
  · decide +kernel

private noncomputable def witness080 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row445

private theorem row080 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 80 (0, 0)) ((rowsAt 10).getD 80 (0, 0)) := by
  apply of_certificate witness080
  · decide +kernel
  · decide +kernel

private noncomputable def witness081 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row194

private theorem row081 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 81 (0, 0)) ((rowsAt 10).getD 81 (0, 0)) := by
  apply of_certificate witness081
  · decide +kernel
  · decide +kernel

private noncomputable def witness082 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row455

private theorem row082 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 82 (0, 0)) ((rowsAt 10).getD 82 (0, 0)) := by
  apply of_certificate witness082
  · decide +kernel
  · decide +kernel

private noncomputable def witness083 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row461

private theorem row083 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 83 (0, 0)) ((rowsAt 10).getD 83 (0, 0)) := by
  apply of_certificate witness083
  · decide +kernel
  · decide +kernel

private noncomputable def witness084 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row468

private theorem row084 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 84 (0, 0)) ((rowsAt 10).getD 84 (0, 0)) := by
  apply of_certificate witness084
  · decide +kernel
  · decide +kernel

private noncomputable def witness085 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row023

private theorem row085 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 85 (0, 0)) ((rowsAt 10).getD 85 (0, 0)) := by
  apply of_certificate witness085
  · decide +kernel
  · decide +kernel

private noncomputable def witness086 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row480

private theorem row086 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 86 (0, 0)) ((rowsAt 10).getD 86 (0, 0)) := by
  apply of_certificate witness086
  · decide +kernel
  · decide +kernel

private noncomputable def witness087 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row209

private theorem row087 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 87 (0, 0)) ((rowsAt 10).getD 87 (0, 0)) := by
  apply of_certificate witness087
  · decide +kernel
  · decide +kernel

private noncomputable def witness088 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row490

private theorem row088 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 88 (0, 0)) ((rowsAt 10).getD 88 (0, 0)) := by
  apply of_certificate witness088
  · decide +kernel
  · decide +kernel

private noncomputable def witness089 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row496

private theorem row089 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 89 (0, 0)) ((rowsAt 10).getD 89 (0, 0)) := by
  apply of_certificate witness089
  · decide +kernel
  · decide +kernel

private noncomputable def witness090 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row024

private theorem row090 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 90 (0, 0)) ((rowsAt 10).getD 90 (0, 0)) := by
  apply of_certificate witness090
  · decide +kernel
  · decide +kernel

private noncomputable def witness091 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row219

private theorem row091 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 91 (0, 0)) ((rowsAt 10).getD 91 (0, 0)) := by
  apply of_certificate witness091
  · decide +kernel
  · decide +kernel

private noncomputable def witness092 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row513

private theorem row092 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 92 (0, 0)) ((rowsAt 10).getD 92 (0, 0)) := by
  apply of_certificate witness092
  · decide +kernel
  · decide +kernel

private noncomputable def witness093 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row519

private theorem row093 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 93 (0, 0)) ((rowsAt 10).getD 93 (0, 0)) := by
  apply of_certificate witness093
  · decide +kernel
  · decide +kernel

private noncomputable def witness094 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row025

private theorem row094 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 94 (0, 0)) ((rowsAt 10).getD 94 (0, 0)) := by
  apply of_certificate witness094
  · decide +kernel
  · decide +kernel

private noncomputable def witness095 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row531

private theorem row095 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 95 (0, 0)) ((rowsAt 10).getD 95 (0, 0)) := by
  apply of_certificate witness095
  · decide +kernel
  · decide +kernel

private noncomputable def witness096 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row534

private theorem row096 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 96 (0, 0)) ((rowsAt 10).getD 96 (0, 0)) := by
  apply of_certificate witness096
  · decide +kernel
  · decide +kernel

private noncomputable def witness097 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row026

private theorem row097 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 97 (0, 0)) ((rowsAt 10).getD 97 (0, 0)) := by
  apply of_certificate witness097
  · decide +kernel
  · decide +kernel

private noncomputable def witness098 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row546

private theorem row098 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 98 (0, 0)) ((rowsAt 10).getD 98 (0, 0)) := by
  apply of_certificate witness098
  · decide +kernel
  · decide +kernel

private noncomputable def witness099 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row237

private theorem row099 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 99 (0, 0)) ((rowsAt 10).getD 99 (0, 0)) := by
  apply of_certificate witness099
  · decide +kernel
  · decide +kernel

private noncomputable def witness100 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row556

private theorem row100 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 100 (0, 0)) ((rowsAt 10).getD 100 (0, 0)) := by
  apply of_certificate witness100
  · decide +kernel
  · decide +kernel

private noncomputable def witness101 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row242

private theorem row101 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 101 (0, 0)) ((rowsAt 10).getD 101 (0, 0)) := by
  apply of_certificate witness101
  · decide +kernel
  · decide +kernel

private noncomputable def witness102 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row567

private theorem row102 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 102 (0, 0)) ((rowsAt 10).getD 102 (0, 0)) := by
  apply of_certificate witness102
  · decide +kernel
  · decide +kernel

private noncomputable def witness103 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row573

private theorem row103 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 103 (0, 0)) ((rowsAt 10).getD 103 (0, 0)) := by
  apply of_certificate witness103
  · decide +kernel
  · decide +kernel

private noncomputable def witness104 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row028

private theorem row104 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 104 (0, 0)) ((rowsAt 10).getD 104 (0, 0)) := by
  apply of_certificate witness104
  · decide +kernel
  · decide +kernel

private noncomputable def witness105 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row585

private theorem row105 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 105 (0, 0)) ((rowsAt 10).getD 105 (0, 0)) := by
  apply of_certificate witness105
  · decide +kernel
  · decide +kernel

private noncomputable def witness106 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row588

private theorem row106 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 106 (0, 0)) ((rowsAt 10).getD 106 (0, 0)) := by
  apply of_certificate witness106
  · decide +kernel
  · decide +kernel

private noncomputable def witness107 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row029

private theorem row107 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 107 (0, 0)) ((rowsAt 10).getD 107 (0, 0)) := by
  apply of_certificate witness107
  · decide +kernel
  · decide +kernel

private noncomputable def witness108 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row600

private theorem row108 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 108 (0, 0)) ((rowsAt 10).getD 108 (0, 0)) := by
  apply of_certificate witness108
  · decide +kernel
  · decide +kernel

private noncomputable def witness109 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row260

private theorem row109 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 109 (0, 0)) ((rowsAt 10).getD 109 (0, 0)) := by
  apply of_certificate witness109
  · decide +kernel
  · decide +kernel

private noncomputable def witness110 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row610

private theorem row110 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 110 (0, 0)) ((rowsAt 10).getD 110 (0, 0)) := by
  apply of_certificate witness110
  · decide +kernel
  · decide +kernel

private noncomputable def witness111 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row616

private theorem row111 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 111 (0, 0)) ((rowsAt 10).getD 111 (0, 0)) := by
  apply of_certificate witness111
  · decide +kernel
  · decide +kernel

private noncomputable def witness112 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row623

private theorem row112 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 112 (0, 0)) ((rowsAt 10).getD 112 (0, 0)) := by
  apply of_certificate witness112
  · decide +kernel
  · decide +kernel

private noncomputable def witness113 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row031

private theorem row113 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 113 (0, 0)) ((rowsAt 10).getD 113 (0, 0)) := by
  apply of_certificate witness113
  · decide +kernel
  · decide +kernel

private noncomputable def witness114 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row635

private theorem row114 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 114 (0, 0)) ((rowsAt 10).getD 114 (0, 0)) := by
  apply of_certificate witness114
  · decide +kernel
  · decide +kernel

private noncomputable def witness115 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row275

private theorem row115 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 115 (0, 0)) ((rowsAt 10).getD 115 (0, 0)) := by
  apply of_certificate witness115
  · decide +kernel
  · decide +kernel

private noncomputable def witness116 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row645

private theorem row116 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 116 (0, 0)) ((rowsAt 10).getD 116 (0, 0)) := by
  apply of_certificate witness116
  · decide +kernel
  · decide +kernel

private noncomputable def witness117 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row651

private theorem row117 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 117 (0, 0)) ((rowsAt 10).getD 117 (0, 0)) := by
  apply of_certificate witness117
  · decide +kernel
  · decide +kernel

private noncomputable def witness118 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row032

private theorem row118 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 118 (0, 0)) ((rowsAt 10).getD 118 (0, 0)) := by
  apply of_certificate witness118
  · decide +kernel
  · decide +kernel

private noncomputable def witness119 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row285

private theorem row119 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 119 (0, 0)) ((rowsAt 10).getD 119 (0, 0)) := by
  apply of_certificate witness119
  · decide +kernel
  · decide +kernel

private noncomputable def witness120 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row668

private theorem row120 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 120 (0, 0)) ((rowsAt 10).getD 120 (0, 0)) := by
  apply of_certificate witness120
  · decide +kernel
  · decide +kernel

private noncomputable def witness121 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row674

private theorem row121 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 121 (0, 0)) ((rowsAt 10).getD 121 (0, 0)) := by
  apply of_certificate witness121
  · decide +kernel
  · decide +kernel

private noncomputable def witness122 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row033

private theorem row122 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 122 (0, 0)) ((rowsAt 10).getD 122 (0, 0)) := by
  apply of_certificate witness122
  · decide +kernel
  · decide +kernel

private noncomputable def witness123 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row686

private theorem row123 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 123 (0, 0)) ((rowsAt 10).getD 123 (0, 0)) := by
  apply of_certificate witness123
  · decide +kernel
  · decide +kernel

private noncomputable def witness124 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row689

private theorem row124 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 124 (0, 0)) ((rowsAt 10).getD 124 (0, 0)) := by
  apply of_certificate witness124
  · decide +kernel
  · decide +kernel

private noncomputable def witness125 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row034

private theorem row125 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 125 (0, 0)) ((rowsAt 10).getD 125 (0, 0)) := by
  apply of_certificate witness125
  · decide +kernel
  · decide +kernel

private noncomputable def witness126 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row701

private theorem row126 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 126 (0, 0)) ((rowsAt 10).getD 126 (0, 0)) := by
  apply of_certificate witness126
  · decide +kernel
  · decide +kernel

private noncomputable def witness127 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row303

private theorem row127 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 127 (0, 0)) ((rowsAt 10).getD 127 (0, 0)) := by
  apply of_certificate witness127
  · decide +kernel
  · decide +kernel

private noncomputable def witness128 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row711

private theorem row128 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 128 (0, 0)) ((rowsAt 10).getD 128 (0, 0)) := by
  apply of_certificate witness128
  · decide +kernel
  · decide +kernel

private noncomputable def witness129 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row308

private theorem row129 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 129 (0, 0)) ((rowsAt 10).getD 129 (0, 0)) := by
  apply of_certificate witness129
  · decide +kernel
  · decide +kernel

private noncomputable def witness130 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row722

private theorem row130 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 130 (0, 0)) ((rowsAt 10).getD 130 (0, 0)) := by
  apply of_certificate witness130
  · decide +kernel
  · decide +kernel

private noncomputable def witness131 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row728

private theorem row131 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 131 (0, 0)) ((rowsAt 10).getD 131 (0, 0)) := by
  apply of_certificate witness131
  · decide +kernel
  · decide +kernel

private noncomputable def witness132 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row036

private theorem row132 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 132 (0, 0)) ((rowsAt 10).getD 132 (0, 0)) := by
  apply of_certificate witness132
  · decide +kernel
  · decide +kernel

private noncomputable def witness133 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row740

private theorem row133 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 133 (0, 0)) ((rowsAt 10).getD 133 (0, 0)) := by
  apply of_certificate witness133
  · decide +kernel
  · decide +kernel

private noncomputable def witness134 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row743

private theorem row134 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 134 (0, 0)) ((rowsAt 10).getD 134 (0, 0)) := by
  apply of_certificate witness134
  · decide +kernel
  · decide +kernel

private noncomputable def witness135 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row037

private theorem row135 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 135 (0, 0)) ((rowsAt 10).getD 135 (0, 0)) := by
  apply of_certificate witness135
  · decide +kernel
  · decide +kernel

private noncomputable def witness136 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row755

private theorem row136 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 136 (0, 0)) ((rowsAt 10).getD 136 (0, 0)) := by
  apply of_certificate witness136
  · decide +kernel
  · decide +kernel

private noncomputable def witness137 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row326

private theorem row137 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 137 (0, 0)) ((rowsAt 10).getD 137 (0, 0)) := by
  apply of_certificate witness137
  · decide +kernel
  · decide +kernel

private noncomputable def witness138 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row765

private theorem row138 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 138 (0, 0)) ((rowsAt 10).getD 138 (0, 0)) := by
  apply of_certificate witness138
  · decide +kernel
  · decide +kernel

private noncomputable def witness139 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row771

private theorem row139 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 139 (0, 0)) ((rowsAt 10).getD 139 (0, 0)) := by
  apply of_certificate witness139
  · decide +kernel
  · decide +kernel

private noncomputable def witness140 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row778

private theorem row140 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 140 (0, 0)) ((rowsAt 10).getD 140 (0, 0)) := by
  apply of_certificate witness140
  · decide +kernel
  · decide +kernel

private noncomputable def witness141 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row039

private theorem row141 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 141 (0, 0)) ((rowsAt 10).getD 141 (0, 0)) := by
  apply of_certificate witness141
  · decide +kernel
  · decide +kernel

private noncomputable def witness142 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row790

private theorem row142 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 142 (0, 0)) ((rowsAt 10).getD 142 (0, 0)) := by
  apply of_certificate witness142
  · decide +kernel
  · decide +kernel

private noncomputable def witness143 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row341

private theorem row143 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 143 (0, 0)) ((rowsAt 10).getD 143 (0, 0)) := by
  apply of_certificate witness143
  · decide +kernel
  · decide +kernel

private noncomputable def witness144 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row800

private theorem row144 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 144 (0, 0)) ((rowsAt 10).getD 144 (0, 0)) := by
  apply of_certificate witness144
  · decide +kernel
  · decide +kernel

private noncomputable def witness145 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row806

private theorem row145 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 145 (0, 0)) ((rowsAt 10).getD 145 (0, 0)) := by
  apply of_certificate witness145
  · decide +kernel
  · decide +kernel

private noncomputable def witness146 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row040

private theorem row146 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 146 (0, 0)) ((rowsAt 10).getD 146 (0, 0)) := by
  apply of_certificate witness146
  · decide +kernel
  · decide +kernel

private noncomputable def witness147 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row351

private theorem row147 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 147 (0, 0)) ((rowsAt 10).getD 147 (0, 0)) := by
  apply of_certificate witness147
  · decide +kernel
  · decide +kernel

private noncomputable def witness148 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row823

private theorem row148 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 148 (0, 0)) ((rowsAt 10).getD 148 (0, 0)) := by
  apply of_certificate witness148
  · decide +kernel
  · decide +kernel

private noncomputable def witness149 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row829

private theorem row149 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 149 (0, 0)) ((rowsAt 10).getD 149 (0, 0)) := by
  apply of_certificate witness149
  · decide +kernel
  · decide +kernel

private noncomputable def witness150 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row041

private theorem row150 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 150 (0, 0)) ((rowsAt 10).getD 150 (0, 0)) := by
  apply of_certificate witness150
  · decide +kernel
  · decide +kernel

private noncomputable def witness151 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row841

private theorem row151 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 151 (0, 0)) ((rowsAt 10).getD 151 (0, 0)) := by
  apply of_certificate witness151
  · decide +kernel
  · decide +kernel

private noncomputable def witness152 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row844

private theorem row152 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 152 (0, 0)) ((rowsAt 10).getD 152 (0, 0)) := by
  apply of_certificate witness152
  · decide +kernel
  · decide +kernel

private noncomputable def witness153 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row042

private theorem row153 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 153 (0, 0)) ((rowsAt 10).getD 153 (0, 0)) := by
  apply of_certificate witness153
  · decide +kernel
  · decide +kernel

private noncomputable def witness154 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row856

private theorem row154 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 154 (0, 0)) ((rowsAt 10).getD 154 (0, 0)) := by
  apply of_certificate witness154
  · decide +kernel
  · decide +kernel

private noncomputable def witness155 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row861

private theorem row155 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 155 (0, 0)) ((rowsAt 10).getD 155 (0, 0)) := by
  apply of_certificate witness155
  · decide +kernel
  · decide +kernel

private noncomputable def witness156 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row043

private theorem row156 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 156 (0, 0)) ((rowsAt 10).getD 156 (0, 0)) := by
  apply of_certificate witness156
  · decide +kernel
  · decide +kernel

private noncomputable def witness157 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row873

private theorem row157 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 157 (0, 0)) ((rowsAt 10).getD 157 (0, 0)) := by
  apply of_certificate witness157
  · decide +kernel
  · decide +kernel

private noncomputable def witness158 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row376

private theorem row158 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 158 (0, 0)) ((rowsAt 10).getD 158 (0, 0)) := by
  apply of_certificate witness158
  · decide +kernel
  · decide +kernel

private noncomputable def witness159 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row883

private theorem row159 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 159 (0, 0)) ((rowsAt 10).getD 159 (0, 0)) := by
  apply of_certificate witness159
  · decide +kernel
  · decide +kernel

private noncomputable def witness160 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row889

private theorem row160 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 160 (0, 0)) ((rowsAt 10).getD 160 (0, 0)) := by
  apply of_certificate witness160
  · decide +kernel
  · decide +kernel

private noncomputable def witness161 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row044

private theorem row161 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 161 (0, 0)) ((rowsAt 10).getD 161 (0, 0)) := by
  apply of_certificate witness161
  · decide +kernel
  · decide +kernel

private noncomputable def witness162 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row386

private theorem row162 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 162 (0, 0)) ((rowsAt 10).getD 162 (0, 0)) := by
  apply of_certificate witness162
  · decide +kernel
  · decide +kernel

private noncomputable def witness163 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add Basis07.row001 (add node02364 (t Basis07.row006))) (add (add node00414 (t Basis07.row009)) (add (t Basis07.row010) Basis07.row012))) (add (add (add node00990 (t Basis07.row015)) (add (t Basis07.row016) node02514)) (add (add node01385 (t Basis07.row022)) (add node02273 (t Basis07.row025))))) (add (add (add (add Basis07.row029 node01539) (add (t Basis07.row033) Basis07.row035)) (add (add Basis07.row036 (t Basis07.row037)) (add (t Basis07.row038) node03669))) (add (add (add Basis07.row042 (t Basis07.row042)) (add Basis07.row044 Basis07.row045)) (add (add (t Basis07.row046) Basis07.row048) (add Basis07.row050 (t Basis07.row051)))))) (add (add (add (add node01758 (add node02690 Basis07.row056)) (add (add (t Basis07.row058) node00891) (add Basis07.row062 Basis07.row064))) (add (add (add node02654 node01759) (add node02740 node02442)) (add (add (t Basis07.row073) (t Basis07.row074)) (add (t Basis07.row075) node00609)))) (add (add (add (add (t Basis07.row078) Basis07.row081) (add Basis07.row082 node02068)) (add (add node03670 Basis07.row092) (add node03752 Basis07.row097))) (add (add (add node00378 Basis07.row100) (add node02277 node00753)) (add (add node02689 node00513) (add (t Basis07.row109) node00627)))))) (add (add (add (add (add Basis07.row112 (add node00286 node03153)) (add (add node01386 node00840) (add (t Basis07.row124) Basis07.row126))) (add (add (add Basis07.row127 (t Basis07.row127)) (add (t Basis07.row128) (t Basis07.row131))) (add (add Basis07.row133 node00560) (add node02044 node01430)))) (add (add (add (add node00536 node00107) (add (t Basis07.row144) (t Basis07.row146))) (add (add (t Basis07.row147) Basis07.row149) (add node02095 node01704))) (add (add (add Basis07.row154 Basis07.row155) (add node03251 node03014)) (add (add node00537 node01165) (add (t Basis07.row164) Basis07.row165))))) (add (add (add (add (add (t Basis07.row166) node02370) (add (t Basis07.row169) Basis07.row172)) (add (add Basis07.row173 Basis07.row174) (add Basis07.row175 (t Basis07.row176)))) (add (add (add Basis07.row178 Basis07.row179) (add node01919 Basis07.row184)) (add (add node00498 (t Basis07.row187)) (add Basis07.row188 Basis07.row189)))) (add (add (add (add Basis07.row190 node03347) (add node02589 node01363)) (add (add node02734 Basis07.row199) (add node01696 node00826))) (add (add (add node00765 (t Basis07.row208)) (add node00394 Basis07.row213)) (add (add node04490 (t Basis07.row216)) (add node01153 node01453))))))) (add (add (add (add (add (add (t Basis07.row220) (add (t Basis07.row222) node03045)) (add (add (t Basis07.row225) (t Basis07.row226)) (add node01858 Basis07.row230))) (add (add (add Basis07.row231 (t Basis07.row231)) (add node03886 node02642)) (add (add (t Basis07.row239) Basis07.row240) (add node01089 (t Basis07.row244))))) (add (add (add (add node00011 (t Basis07.row247)) (add (t Basis07.row248) (t Basis07.row249))) (add (add Basis07.row251 (t Basis07.row253)) (add Basis07.row254 Basis07.row256))) (add (add (add (t Basis07.row256) (t Basis07.row259)) (add Basis07.row261 node01341)) (add (add node01892 Basis07.row267) (add (t Basis07.row267) node02147))))) (add (add (add (add (add (t Basis07.row270) node01413) (add node00272 (t Basis07.row275))) (add (add (t Basis07.row276) (t Basis07.row279)) (add (t Basis07.row281) (t Basis07.row282)))) (add (add (add node03357 node00540) (add node02510 node02051)) (add (add node04492 (t Basis07.row293)) (add (t Basis07.row294) node02097)))) (add (add (add (add node00562 node02574) (add (t Basis07.row302) node00792)) (add (add Basis07.row306 (t Basis07.row306)) (add node01769 Basis07.row310))) (add (add (add Basis07.row311 node01208) (add node00867 node00868)) (add (add node00119 node01047) (add node00172 node00400)))))) (add (add (add (add (add node03761 (add node01732 (t Basis07.row329))) (add (add Basis07.row330 Basis07.row331) (add (t Basis07.row332) (t Basis07.row333)))) (add (add (add Basis07.row334 Basis07.row335) (add (t Basis07.row337) (t Basis07.row338))) (add (add node01654 (t Basis07.row342)) (add Basis07.row343 node00597)))) (add (add (add (add Basis07.row346 (t Basis07.row346)) (add Basis07.row349 (t Basis07.row349))) (add (add Basis07.row351 node02920) (add node02411 node00077))) (add (add (add (t Basis07.row358) Basis07.row359) (add (t Basis07.row362) Basis07.row365)) (add (add Basis07.row366 node00226) (add Basis07.row368 node02262))))) (add (add (add (add (add Basis07.row372 node04044) (add node00038 Basis07.row378)) (add (add (t Basis07.row379) node01168) (add node02560 node04058))) (add (add (add node00809 (t Basis07.row388)) (add (t Basis07.row389) (t Basis07.row391))) (add (add node02539 Basis07.row395) (add node01957 node03449)))) (add (add (add (add Basis07.row400 node00720) (add node00630 node01713)) (add (add Basis07.row408 (t Basis07.row409)) (add (t Basis07.row410) node00337))) (add (add (add Basis07.row415 (t Basis07.row415)) (add Basis07.row420 (t Basis07.row420))) (add (add node01833 Basis07.row423) (add node03091 node01771)))))))) (add (add (add (add (add (add (add node00522 (add (t Basis07.row430) node02842)) (add (add (t Basis07.row434) node01073) (add Basis07.row439 Basis07.row440))) (add (add (add Basis07.row441 (t Basis07.row441)) (add node03379 (t Basis07.row445))) (add (add Basis07.row446 Basis07.row447) (add Basis07.row448 Basis07.row450)))) (add (add (add (add Basis07.row451 (t Basis07.row452)) (add node02349 (t Basis07.row456))) (add (add node00068 node01936) (add (t Basis07.row462) (t Basis07.row463)))) (add (add (add node01092 (t Basis07.row465)) (add node01418 Basis07.row469)) (add (add (t Basis07.row470) Basis07.row472) (add node01440 Basis07.row476))))) (add (add (add (add node00600 (add Basis07.row480 Basis07.row481)) (add (add node00698 node01987) (add (t Basis07.row486) (t Basis07.row488)))) (add (add (add (t Basis07.row489) node03115) (add (t Basis07.row494) node01839)) (add (add (t Basis07.row499) (t Basis07.row503)) (add Basis07.row507 Basis07.row509)))) (add (add (add (add node00588 (t Basis07.row512)) (add Basis07.row513 node01565)) (add (add node03687 node03454) (add Basis07.row521 (t Basis07.row522)))) (add (add (add node00488 node03116) (add (t Basis07.row529) (t Basis07.row530))) (add (add node02109 Basis07.row535) (add Basis07.row536 Basis07.row537)))))) (add (add (add (add (add node01036 (add Basis07.row542 node01547)) (add (add (t Basis07.row545) node03728) (add (t Basis07.row549) Basis07.row550))) (add (add (add node03117 node00450) (add node03135 (t Basis07.row556))) (add (add node01271 node04361) (add node00139 (t Basis07.row565))))) (add (add (add (add Basis07.row567 Basis07.row568) (add node03345 Basis07.row572)) (add (add Basis07.row574 node02039) (add Basis07.row579 (t Basis07.row579)))) (add (add (add node01608 node02400) (add (t Basis07.row585) Basis07.row586)) (add (add node00973 node00810) (add Basis07.row596 Basis07.row597))))) (add (add (add (add (add node00956 node01330) (add node00322 Basis07.row603)) (add (add (t Basis07.row603) node00764) (add (t Basis07.row607) (t Basis07.row609)))) (add (add (add node00033 Basis07.row613) (add node00159 node01245)) (add (add node01806 node00716) (add (t Basis07.row626) (t Basis07.row627))))) (add (add (add (add (t Basis07.row629) node00198) (add node01117 node01017)) (add (add Basis07.row637 node04161) (add (t Basis07.row642) node03145))) (add (add (add node02300 node04181) (add (t Basis07.row654) node01807)) (add (add node01845 Basis07.row659) (add node00433 node02769))))))) (add (add (add (add (add (add Basis07.row666 (add node00944 node01123)) (add (add Basis07.row672 Basis07.row673) (add Basis07.row675 node00185))) (add (add (add (t Basis07.row677) node03333) (add node00052 node03475)) (add (add (t Basis07.row686) (t Basis07.row687)) (add node01965 node02338)))) (add (add (add (add Basis07.row695 node01580) (add Basis07.row698 node03579)) (add (add (t Basis07.row702) node01848) (add (t Basis07.row706) Basis07.row708))) (add (add (add node03780 node01304) (add node01902 node01462)) (add (add (t Basis07.row717) node00142) (add Basis07.row721 Basis07.row722))))) (add (add (add (add (add node01402 (t Basis07.row725)) (add Basis07.row726 node00325)) (add (add node01904 (t Basis07.row730)) (add node01186 (t Basis07.row734)))) (add (add (add (t Basis07.row735) node03997) (add (t Basis07.row738) Basis07.row741)) (add (add Basis07.row742 Basis07.row744) (add node03167 Basis07.row748)))) (add (add (add (add Basis07.row749 Basis07.row750) (add node00508 node02160)) (add (add (t Basis07.row754) node00530) (add node01980 Basis07.row759))) (add (add (add node00062 (t Basis07.row763)) (add (t Basis07.row764) node02585)) (add (add node00387 Basis07.row771) (add node02167 node00102)))))) (add (add (add (add (add node00004 (add node02014 node04428)) (add (add Basis07.row783 node02270) (add node02201 Basis07.row789))) (add (add (add (t Basis07.row790) Basis07.row791) (add node00188 Basis07.row796)) (add (add Basis07.row798 node00925) (add node02895 Basis07.row802)))) (add (add (add (add Basis07.row803 Basis07.row804) (add Basis07.row805 (t Basis07.row807))) (add (add node02919 node02017) (add node00986 node01808))) (add (add (add (t Basis07.row817) Basis07.row821) (add node02022 node01347)) (add (add Basis07.row828 node02065) (add (t Basis07.row833) node01019))))) (add (add (add (add (add Basis07.row838 Basis07.row840) (add (t Basis07.row842) Basis07.row845)) (add (add (t Basis07.row845) node03552) (add (t Basis07.row849) (t Basis07.row851)))) (add (add (add node04432 Basis07.row855) (add node02580 node01512)) (add (add Basis07.row863 (t Basis07.row865)) (add Basis07.row866 Basis07.row868)))) (add (add (add (add node02500 Basis07.row873) (add (t Basis07.row873) node01918)) (add (add node01002 node00581) (add Basis07.row879 node00865))) (add (add (add node00248 node01256) (add node01038 node01082)) (add (add node02501 node02603) (add Basis07.row894 Basis07.row895)))))))))

private theorem row163 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 163 (0, 0)) ((rowsAt 10).getD 163 (0, 0)) := by
  apply of_certificate witness163
  · decide +kernel
  · decide +kernel

private noncomputable def witness164 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add node00582 (add (t Basis07.row002) (t Basis07.row003))) (add (add (t Basis07.row004) node00606) (add Basis07.row006 (t Basis07.row007)))) (add (add (add node01234 node01886) (add node00071 node00807)) (add (add (t Basis07.row017) node01385) (add node01474 node03750)))) (add (add (add node00559 (add node00866 node02440)) (add (add Basis07.row031 (t Basis07.row033)) (add Basis07.row035 Basis07.row036))) (add (add (add node03413 (t Basis07.row040)) (add Basis07.row041 (t Basis07.row041))) (add (add (t Basis07.row043) (t Basis07.row044)) (add node00857 node00026))))) (add (add (add (add node01874 (add Basis07.row052 (t Basis07.row055))) (add (add Basis07.row056 node01578) (add (t Basis07.row060) Basis07.row061))) (add (add (add Basis07.row063 node00670) (add node00106 node03751)) (add (add node03240 node01174) (add Basis07.row077 node00191)))) (add (add (add node00134 (add node00730 node01791)) (add (add node04173 node02813) (add (t Basis07.row089) (t Basis07.row092)))) (add (add (add Basis07.row094 (t Basis07.row094)) (add Basis07.row097 node01295)) (add (add (t Basis07.row101) node01760) (add (t Basis07.row105) node01009)))))) (add (add (add (add (add node00147 (add node00237 node01022)) (add (add node01087 node01074) (add node01242 node00437))) (add (add (add node01795 node02436) (add (t Basis07.row129) node04048)) (add (add Basis07.row134 Basis07.row135) (add node02044 node04397)))) (add (add (add (t Basis07.row140) (add node01619 node02806)) (add (add Basis07.row148 node00927) (add (t Basis07.row153) Basis07.row154))) (add (add (add Basis07.row155 Basis07.row158) (add node03014 Basis07.row161)) (add (add node01165 (t Basis07.row164)) (add Basis07.row165 Basis07.row166))))) (add (add (add (add node03832 (add (t Basis07.row171) (t Basis07.row172))) (add (add node00205 node03414) (add (t Basis07.row178) (t Basis07.row179)))) (add (add (add node00239 node02328) (add node00594 node01692)) (add (add node00802 node02608) (add node04483 Basis07.row193)))) (add (add (add (add (t Basis07.row195) (t Basis07.row197)) (add Basis07.row200 Basis07.row202)) (add (add (t Basis07.row202) node03370) (add (t Basis07.row205) node01334))) (add (add (add (t Basis07.row211) (t Basis07.row212)) (add node04490 (t Basis07.row217))) (add (add node00517 (t Basis07.row220)) (add node00066 node00094))))))) (add (add (add (add (add (add (t Basis07.row226) (add Basis07.row228 node02783)) (add (add node00365 (t Basis07.row233)) (add Basis07.row234 (t Basis07.row235)))) (add (add (add node02869 node01025) (add node00499 node01502)) (add (add Basis07.row246 node02614) (add node03625 node01244)))) (add (add (add node00481 (add node02795 Basis07.row260)) (add (add (t Basis07.row260) Basis07.row263) (add node02605 (t Basis07.row265)))) (add (add (add node03254 Basis07.row269) (add node00851 node02512)) (add (add node00952 node03952) (add Basis07.row278 (t Basis07.row280)))))) (add (add (add (add Basis07.row281 (add Basis07.row283 node03357)) (add (add (t Basis07.row286) node01810) (add node01259 Basis07.row291))) (add (add (add Basis07.row292 Basis07.row295) (add (t Basis07.row297) (t Basis07.row298))) (add (add (t Basis07.row301) node00792) (add node01932 Basis07.row308)))) (add (add (add (add (t Basis07.row308) node02626) (add (t Basis07.row311) node00867)) (add (add (t Basis07.row314) node03679) (add node01047 Basis07.row321))) (add (add (add Basis07.row322 (t Basis07.row322)) (add node03058 (t Basis07.row326))) (add (add Basis07.row330 node00906) (add node00686 node01333)))))) (add (add (add (add (add Basis07.row336 (add node00995 node00687)) (add (add (t Basis07.row342) Basis07.row343) (add Basis07.row345 (t Basis07.row346)))) (add (add (add node02099 (t Basis07.row350)) (add Basis07.row353 Basis07.row354)) (add (add node00611 node01267) (add (t Basis07.row358) (t Basis07.row359))))) (add (add (add (t Basis07.row362) (add Basis07.row363 Basis07.row365)) (add (add node03436 node01998) (add (t Basis07.row370) (t Basis07.row371)))) (add (add (add node01811 node01199) (add node00444 (t Basis07.row377))) (add (add node01168 Basis07.row382) (add (t Basis07.row385) Basis07.row386))))) (add (add (add (add (t Basis07.row386) (add node02427 (t Basis07.row389))) (add (add node01999 Basis07.row394) (add (t Basis07.row394) node02263))) (add (add (add node01132 (t Basis07.row401)) (add Basis07.row403 Basis07.row404)) (add (add Basis07.row405 node04409) (add Basis07.row410 node02102)))) (add (add (add (add Basis07.row414 node01454) (add node02413 Basis07.row419)) (add (add Basis07.row420 node00565) (add node02153 (t Basis07.row424)))) (add (add (add (t Basis07.row425) node02988) (add node01834 node03419)) (add (add (t Basis07.row433) node00138) (add (t Basis07.row436) node00027)))))))) (add (add (add (add (add (add (add (t Basis07.row439) (add (t Basis07.row440) (t Basis07.row441))) (add (add node02269 node01689) (add node03569 (t Basis07.row451)))) (add (add (add Basis07.row453 (t Basis07.row453)) (add node02001 (t Basis07.row458))) (add (add node01881 node00464) (add Basis07.row464 node03159)))) (add (add (add Basis07.row467 (add Basis07.row468 node01659)) (add (add (t Basis07.row472) (t Basis07.row475)) (add Basis07.row478 Basis07.row479))) (add (add (add Basis07.row480 Basis07.row481) (add node00154 node01107)) (add (add node02576 Basis07.row487) (add node00813 node01069))))) (add (add (add (add (t Basis07.row491) (add node03685 (t Basis07.row496))) (add (add (t Basis07.row497) (t Basis07.row499)) (add node01661 Basis07.row502))) (add (add (add node04377 node00099) (add node01311 (t Basis07.row513))) (add (add node02379 Basis07.row519) (add (t Basis07.row520) (t Basis07.row523))))) (add (add (add Basis07.row524 (add Basis07.row525 node04357)) (add (add Basis07.row530 node02397) (add node01196 node01663))) (add (add (add node02451 (t Basis07.row540)) (add node01063 node00526)) (add (add Basis07.row546 (t Basis07.row547)) (add node00983 Basis07.row551)))))) (add (add (add (add (add Basis07.row553 (add Basis07.row554 (t Basis07.row556))) (add (add node02006 node04366) (add node02730 (t Basis07.row565)))) (add (add (add node03225 node01016) (add node00039 node02398)) (add (add (t Basis07.row575) (t Basis07.row577)) (add (t Basis07.row578) node01197)))) (add (add (add Basis07.row581 (add (t Basis07.row581) (t Basis07.row582))) (add (add Basis07.row584 Basis07.row585) (add Basis07.row586 node01459))) (add (add (add node00973 node03065) (add node01898 (t Basis07.row595))) (add (add Basis07.row596 node00489) (add node01330 node01189))))) (add (add (add (add node00344 (add node01814 (t Basis07.row606))) (add (add Basis07.row607 node01031) (add (t Basis07.row610) (t Basis07.row611)))) (add (add (add Basis07.row612 (t Basis07.row612)) (add node00913 (t Basis07.row615))) (add (add (t Basis07.row617) Basis07.row619) (add node00184 node01569)))) (add (add (add (add (t Basis07.row625) node01466) (add (t Basis07.row629) node02010)) (add (add node02837 (t Basis07.row637)) (add node04341 Basis07.row640))) (add (add (add node02195 Basis07.row644) (add node01665 (t Basis07.row647))) (add (add node00490 node00923) (add node01812 node01096))))))) (add (add (add (add (add (add Basis07.row658 (add (t Basis07.row659) (t Basis07.row660))) (add (add node02196 node00924) (add (t Basis07.row668) (t Basis07.row669)))) (add (add (add Basis07.row670 Basis07.row671) (add (t Basis07.row671) node00373)) (add (add (t Basis07.row674) (t Basis07.row675)) (add (t Basis07.row676) node03990)))) (add (add (add node00385 (add Basis07.row683 Basis07.row685)) (add (add (t Basis07.row686) (t Basis07.row689)) (add node01724 (t Basis07.row695)))) (add (add (add node01489 node03716) (add node00657 Basis07.row702)) (add (add node03398 Basis07.row706) (add node00529 node03319))))) (add (add (add (add node01779 (add node01864 (t Basis07.row715))) (add (add node02380 Basis07.row720) (add node02260 node02133))) (add (add (add (t Basis07.row727) node00278) (add node02159 (t Basis07.row735))) (add (add (t Basis07.row736) node01380) (add node00938 (t Basis07.row742))))) (add (add (add (add node01182 node02418) (add node00295 node01332)) (add (add (t Basis07.row750) node03032) (add node00327 node00352))) (add (add (add node01384 node03462) (add node01680 Basis07.row765)) (add (add Basis07.row766 node02161) (add Basis07.row770 node00389)))))) (add (add (add (add (add node00328 (add Basis07.row777 (t Basis07.row777))) (add (add node02139 (t Basis07.row780)) (add node00700 node02023))) (add (add (add (t Basis07.row786) (t Basis07.row787)) (add (t Basis07.row788) node02015)) (add (add node01909 Basis07.row795) (add Basis07.row797 (t Basis07.row797))))) (add (add (add (t Basis07.row799) (add node01729 (t Basis07.row803))) (add (add node02499 node03321) (add node04166 node00878))) (add (add (add node02814 node00558) (add Basis07.row822 node01347)) (add (add (t Basis07.row827) node03993) (add node03953 node03141))))) (add (add (add (add node03800 (add node00674 (t Basis07.row841))) (add (add (t Basis07.row842) (t Basis07.row843)) (add node01314 node02952))) (add (add (add (t Basis07.row849) Basis07.row850) (add Basis07.row854 Basis07.row855)) (add (add node02766 node02580) (add (t Basis07.row860) Basis07.row863)))) (add (add (add (add node01574 Basis07.row867) (add node03573 Basis07.row872)) (add (add (t Basis07.row873) node02545) (add node02949 node02595))) (add (add (add Basis07.row883 Basis07.row884) (add node00605 Basis07.row887)) (add (add (t Basis07.row890) Basis07.row891) (add node00169 Basis07.row894)))))))))

private theorem row164 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 164 (0, 0)) ((rowsAt 10).getD 164 (0, 0)) := by
  apply of_certificate witness164
  · decide +kernel
  · decide +kernel

private noncomputable def witness165 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row045

private theorem row165 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 165 (0, 0)) ((rowsAt 10).getD 165 (0, 0)) := by
  apply of_certificate witness165
  · decide +kernel
  · decide +kernel

private noncomputable def witness166 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add (t Basis07.row000) (add Basis07.row002 (t Basis07.row004))) (add (add (t Basis07.row005) (t Basis07.row006)) (add Basis07.row007 node03508))) (add (add (add node04089 node00822) (add node01741 node01360)) (add (add Basis07.row021 (t Basis07.row022)) (add node02323 node00866)))) (add (add (add node02440 (add node00179 node01448)) (add (add node00266 (t Basis07.row036)) (add node00081 node02476))) (add (add (add Basis07.row041 node01324) (add Basis07.row044 Basis07.row045)) (add (add Basis07.row047 node02211) (add (t Basis07.row051) Basis07.row052))))) (add (add (add (add Basis07.row053 (add node01451 node03511)) (add (add (t Basis07.row062) Basis07.row063) (add node01911 node00661))) (add (add (add node02368 Basis07.row071) (add node00608 Basis07.row074)) (add (add Basis07.row075 node01923) (add node04243 Basis07.row082)))) (add (add (add node01791 (add Basis07.row085 Basis07.row086)) (add (add node00377 node00511) (add node01406 node03816))) (add (add (add node01986 (t Basis07.row097)) (add (t Basis07.row099) node01760)) (add (add node00044 (t Basis07.row107)) (add node00147 node02674)))))) (add (add (add (add (add node00222 (add node01993 (t Basis07.row115))) (add (add node03153 Basis07.row122) (add node00437 Basis07.row128))) (add (add (add (t Basis07.row128) node00075) (add node00457 Basis07.row132)) (add (add node03367 (t Basis07.row137)) (add node01317 (t Basis07.row140))))) (add (add (add (t Basis07.row141) (add node01620 Basis07.row145)) (add (add (t Basis07.row145) Basis07.row147) (add node00379 Basis07.row150))) (add (add (add Basis07.row152 Basis07.row153) (add node01646 node01171)) (add (add node01222 Basis07.row162) (add (t Basis07.row162) Basis07.row165))))) (add (add (add (add Basis07.row166 (add (t Basis07.row166) node00380)) (add (add node03674 (t Basis07.row172)) (add (t Basis07.row173) (t Basis07.row174)))) (add (add (add Basis07.row176 (t Basis07.row178)) (add Basis07.row179 node01396)) (add (add node00594 node01472) (add Basis07.row187 Basis07.row189)))) (add (add (add (add Basis07.row190 node02209) (add node00708 Basis07.row197)) (add (add Basis07.row198 node00251) (add node01044 node03370))) (add (add (add node02482 Basis07.row210) (add node00677 node01952)) (add (add node01411 node01153) (add node01453 node02553))))))) (add (add (add (add (add (add Basis07.row223 (add (t Basis07.row224) Basis07.row227)) (add (add Basis07.row228 (t Basis07.row229)) (add (t Basis07.row230) node04271))) (add (add (add Basis07.row235 node01449) (add (t Basis07.row240) node01089)) (add (add node00499 node00396) (add node02673 Basis07.row250)))) (add (add (add node00518 (add node01244 node01464)) (add (add node00419 (t Basis07.row258)) (add (t Basis07.row259) Basis07.row260))) (add (add (add (t Basis07.row260) Basis07.row263) (add node01893 node04112)) (add (add (t Basis07.row267) node01825) (add node03428 Basis07.row273))))) (add (add (add (add Basis07.row274 (add node03444 node01511)) (add (add (t Basis07.row281) node02870) (add (t Basis07.row285) node02625))) (add (add (add Basis07.row289 Basis07.row291) (add Basis07.row292 node01046)) (add (add (t Basis07.row294) (t Basis07.row295)) (add node00207 node02229)))) (add (add (add (add (t Basis07.row300) (t Basis07.row302)) (add (t Basis07.row303) node04349)) (add (add node01769 node02474) (add (t Basis07.row311) Basis07.row313))) (add (add (add node03087 Basis07.row318) (add node03809 Basis07.row322)) (add (add (t Basis07.row322) node01160) (add node03549 Basis07.row328)))))) (add (add (add (add (add Basis07.row332 (add Basis07.row335 (t Basis07.row335))) (add (add (t Basis07.row336) node01827) (add node00542 node00016))) (add (add (add Basis07.row346 (t Basis07.row346)) (add Basis07.row349 (t Basis07.row349))) (add (add node02596 Basis07.row353) (add node02080 (t Basis07.row357))))) (add (add (add node00381 (add node03708 (t Basis07.row364))) (add (add node03472 node00083) (add node01478 node01811))) (add (add (add Basis07.row375 Basis07.row377) (add Basis07.row378 (t Basis07.row378))) (add (add node03523 node02635) (add node03631 node00194))))) (add (add (add (add Basis07.row388 (add (t Basis07.row388) Basis07.row390)) (add (add node01277 Basis07.row394) (add (t Basis07.row395) (t Basis07.row396)))) (add (add (add node02909 Basis07.row402) (add node01443 node00705)) (add (add (t Basis07.row409) Basis07.row411) (add Basis07.row413 (t Basis07.row413))))) (add (add (add (add node02833 node01833) (add Basis07.row423 node03656)) (add (add node02267 (t Basis07.row431)) (add (t Basis07.row432) Basis07.row433))) (add (add (add node00138 (t Basis07.row435)) (add (t Basis07.row437) Basis07.row439)) (add (add Basis07.row440 node01344) (add node03380 Basis07.row446)))))))) (add (add (add (add (add (add (add node00367 (add (t Basis07.row449) node00641)) (add (add node01351 node00315) (add node03884 node02753))) (add (add (add node03531 node00706) (add node03653 Basis07.row472)) (add (add node02727 node02129) (add node00341 node02620)))) (add (add (add node00791 (add Basis07.row483 (t Basis07.row484))) (add (add Basis07.row487 node04027) (add node03114 node03274))) (add (add (add node02797 node02292) (add node00110 (t Basis07.row500))) (add (add Basis07.row501 Basis07.row502) (add node04222 node00448))))) (add (add (add (add Basis07.row508 (add node03872 (t Basis07.row512))) (add (add Basis07.row513 node01015) (add (t Basis07.row517) node00870))) (add (add (add Basis07.row521 (t Basis07.row521)) (add node04347 node00849)) (add (add Basis07.row529 node00156) (add node01721 node03022)))) (add (add (add (add (t Basis07.row536) node01232) (add node00275 Basis07.row542)) (add (add node02135 Basis07.row546) (add (t Basis07.row546) Basis07.row547))) (add (add (add node00983 Basis07.row551) (add Basis07.row553 node01289)) (add (add node00111 node02296) (add (t Basis07.row560) (t Basis07.row561))))))) (add (add (add (add (add Basis07.row562 (add Basis07.row564 node00732)) (add (add node01381 Basis07.row568) (add Basis07.row570 node01775))) (add (add (add Basis07.row573 Basis07.row574) (add node03026 node02652)) (add (add (t Basis07.row581) (t Basis07.row582)) (add node02400 node00899)))) (add (add (add node03775 (add node03957 node01698)) (add (add Basis07.row596 node01146) (add node00527 Basis07.row602))) (add (add (add node02298 (t Basis07.row604)) (add node02116 (t Basis07.row612))) (add (add (t Basis07.row613) node02628) (add node04313 node01643))))) (add (add (add (add node03188 (add node00468 Basis07.row630)) (add (add Basis07.row633 node01179) (add node02838 node01685))) (add (add (add node00305 node00040) (add node03145 node01032)) (add (add node00231 node00923) (add node01488 Basis07.row654)))) (add (add (add (add (t Basis07.row655) Basis07.row656) (add node01845 (t Basis07.row658))) (add (add (t Basis07.row659) node02196) (add (t Basis07.row664) Basis07.row665))) (add (add (add node02456 (t Basis07.row667)) (add Basis07.row668 Basis07.row670)) (add (add Basis07.row671 (t Basis07.row671)) (add node02353 (t Basis07.row674)))))))) (add (add (add (add (add (add (t Basis07.row675) (add (t Basis07.row676) Basis07.row677)) (add (add node03894 node00052) (add node03214 node02416))) (add (add (add node03423 (t Basis07.row690)) (add node03740 node02078)) (add (add Basis07.row699 node03121) (add node01966 (t Basis07.row704))))) (add (add (add node03544 (add (t Basis07.row707) Basis07.row708)) (add (add node00937 node01438) (add Basis07.row713 Basis07.row714))) (add (add (add Basis07.row715 Basis07.row716) (add (t Basis07.row718) node01034)) (add (add node00351 Basis07.row723) (add node03165 node02075))))) (add (add (add (add Basis07.row731 (add Basis07.row732 node01849)) (add (add Basis07.row735 Basis07.row736) (add node02301 (t Basis07.row739)))) (add (add (add Basis07.row740 Basis07.row741) (add node03123 (t Basis07.row745))) (add (add node00003 node00296) (add (t Basis07.row750) (t Basis07.row751))))) (add (add (add (add node02549 node01491) (add node00352 node02246)) (add (add node00201 node00062) (add (t Basis07.row764) node00758))) (add (add (add node02161 (t Basis07.row770)) (add (t Basis07.row771) node02839)) (add (add node04280 node02014) (add (t Basis07.row781) Basis07.row782)))))) (add (add (add (add (add Basis07.row783 (add node02568 (t Basis07.row788))) (add (add (t Basis07.row789) (t Basis07.row790)) (add Basis07.row791 (t Basis07.row792)))) (add (add (add node03637 node01852) (add node00925 node02387)) (add (add (t Basis07.row802) Basis07.row804) (add node03321 node04077)))) (add (add (add Basis07.row812 (add node00622 node00558)) (add (add (t Basis07.row819) Basis07.row821) (add Basis07.row822 Basis07.row823))) (add (add (add (t Basis07.row823) (t Basis07.row824)) (add node03270 (t Basis07.row829))) (add (add (t Basis07.row831) Basis07.row832) (add (t Basis07.row836) (t Basis07.row837)))))) (add (add (add (add node00355 (add (t Basis07.row840) node02422)) (add (add Basis07.row843 Basis07.row845) (add node03704 node00356))) (add (add (add Basis07.row851 node02704) (add node02778 (t Basis07.row858))) (add (add node00265 node01227) (add node00474 Basis07.row865)))) (add (add (add (add (t Basis07.row867) node01003) (add node01590 Basis07.row873)) (add (add node01290 (t Basis07.row876)) (add (t Basis07.row878) node04079))) (add (add (add node00625 node00455) (add node01130 (t Basis07.row887))) (add (add Basis07.row888 node00235) (add node02692 node01970)))))))))

private theorem row166 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 166 (0, 0)) ((rowsAt 10).getD 166 (0, 0)) := by
  apply of_certificate witness166
  · decide +kernel
  · decide +kernel

private noncomputable def witness167 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add node03048 (add node02793 node03050)) (add (add node00414 node02818) (add node01144 node00591))) (add (add (add (t Basis07.row015) (t Basis07.row016)) (add Basis07.row019 node00702)) (add (add node02702 (t Basis07.row024)) (add Basis07.row025 Basis07.row026)))) (add (add (add node00818 (add Basis07.row031 Basis07.row032)) (add (add (t Basis07.row033) (t Basis07.row034)) (add Basis07.row036 node00907))) (add (add (add node01111 Basis07.row042) (add (t Basis07.row042) Basis07.row044)) (add (add (t Basis07.row044) (t Basis07.row045)) (add Basis07.row047 Basis07.row049))))) (add (add (add (add Basis07.row050 (add node00358 node01817)) (add (add (t Basis07.row055) node00072) (add Basis07.row059 Basis07.row060))) (add (add (add (t Basis07.row060) Basis07.row061) (add node01755 (t Basis07.row064))) (add (add node01375 node03440) (add node04392 Basis07.row074)))) (add (add (add (add Basis07.row075 (t Basis07.row076)) (add Basis07.row079 (t Basis07.row079))) (add (add Basis07.row080 node02554) (add node00135 Basis07.row085))) (add (add (add node00377 node00511) (add node00512 (t Basis07.row094))) (add (add node02182 node02310) (add (t Basis07.row099) Basis07.row101)))))) (add (add (add (add (add node02689 (add (t Basis07.row105) node01009)) (add (add node02215 node01435) (add node00362 node03512))) (add (add (add Basis07.row121 Basis07.row122) (add (t Basis07.row123) node00945)) (add (add node00298 node00649) (add node00075 node00010)))) (add (add (add (add (t Basis07.row133) Basis07.row135) (add (t Basis07.row137) (t Basis07.row138))) (add (add node01619 node01639) (add node02433 node00379))) (add (add (add node02179 (t Basis07.row152)) (add Basis07.row153 node02763)) (add (add Basis07.row156 Basis07.row158) (add node00780 node01165))))) (add (add (add (add (t Basis07.row164) (add node03910 Basis07.row167)) (add (add Basis07.row168 Basis07.row170) (add (t Basis07.row170) node00288))) (add (add (add node00205 (t Basis07.row176)) (add (t Basis07.row177) (t Basis07.row179))) (add (add node02280 node02328) (add node00594 node01284)))) (add (add (add (add node03344 (t Basis07.row189)) (add (t Basis07.row190) Basis07.row191)) (add (add node01650 node01340) (add (t Basis07.row197) (t Basis07.row198)))) (add (add (add node03331 node01044) (add node02784 (t Basis07.row205))) (add (add (t Basis07.row207) (t Basis07.row208)) (add node02483 node02371))))))) (add (add (add (add (add (add (t Basis07.row213) (add node03624 node01153)) (add (add node00253 node01953) (add node00704 (t Basis07.row223)))) (add (add (add node03278 node01601) (add node01261 node03227)) (add (add node02228 Basis07.row237) (add node02312 node01025)))) (add (add (add (add node00499 node02484) (add (t Basis07.row246) node00458)) (add (add node01166 node00014) (add node02524 Basis07.row256))) (add (add (add (t Basis07.row257) node00970) (add Basis07.row263 Basis07.row264)) (add (add node01228 node00254) (add (t Basis07.row268) node04302))))) (add (add (add (add node00519 (add Basis07.row274 node00441)) (add (add (t Basis07.row280) Basis07.row281) (add (t Basis07.row284) node04193))) (add (add (add node01259 node01046) (add node00628 Basis07.row297)) (add (add (t Basis07.row297) node00953) (add node00639 (t Basis07.row302))))) (add (add (add (add Basis07.row305 Basis07.row306) (add (t Basis07.row306) (t Basis07.row307))) (add (add Basis07.row310 Basis07.row311) (add node00443 Basis07.row314))) (add (add (add Basis07.row318 (t Basis07.row318)) (add (t Basis07.row319) node02982)) (add (add node01503 (t Basis07.row326)) (add node03301 (t Basis07.row331))))))) (add (add (add (add (add node02434 (add node00120 node00152)) (add (add Basis07.row339 (t Basis07.row340)) (add Basis07.row341 Basis07.row343))) (add (add (add node01357 node00121) (add node00302 node00109)) (add (add (t Basis07.row353) Basis07.row355) (add Basis07.row356 Basis07.row357)))) (add (add (add (add Basis07.row359 node03708) (add Basis07.row363 node03592)) (add (add node00845 node00482) (add node02288 node02896))) (add (add (add node01199 Basis07.row377) (add node03109 node00896)) (add (add Basis07.row383 node00981) (add Basis07.row389 Basis07.row390))))) (add (add (add (add Basis07.row393 (add node00424 (t Basis07.row397))) (add (add (t Basis07.row398) node00630) (add (t Basis07.row404) node04409))) (add (add (add node01280 node01679) (add Basis07.row413 (t Basis07.row413))) (add (add node01321 node03595) (add node04170 node02424)))) (add (add (add (add node03158 Basis07.row427) (add (t Basis07.row429) (t Basis07.row430))) (add (add node01456 Basis07.row434) (add (t Basis07.row434) node04136))) (add (add (add node00781 node01471) (add Basis07.row445 node00640)) (add (add node01184 node00828) (add node04351 node00710)))))))) (add (add (add (add (add (add (add node01239 (add node01936 (t Basis07.row462))) (add (add Basis07.row463 node03046) (add (t Basis07.row467) (t Basis07.row468)))) (add (add (add Basis07.row469 (t Basis07.row470)) (add Basis07.row472 node02727)) (add (add node01716 Basis07.row479) (add node00525 node00154)))) (add (add (add (add Basis07.row483 node01395) (add (t Basis07.row488) node01137)) (add (add (t Basis07.row490) (t Basis07.row493)) (add node02728 Basis07.row500))) (add (add (add Basis07.row502 node00759) (add node00429 node00739)) (add (add node00504 node02234) (add node01628 node03687))))) (add (add (add (add Basis07.row521 (add Basis07.row522 node00897)) (add (add Basis07.row524 node03503) (add (t Basis07.row527) (t Basis07.row528)))) (add (add (add (t Basis07.row529) node01721) (add Basis07.row535 node00431)) (add (add node00871 (t Basis07.row540)) (add (t Basis07.row542) (t Basis07.row543))))) (add (add (add (add node00175 node02801) (add node00943 node01053)) (add (add node02058 (t Basis07.row556)) (add node01271 (t Basis07.row559)))) (add (add (add node02940 node02318) (add (t Basis07.row568) (t Basis07.row569))) (add (add Basis07.row571 Basis07.row572) (add node03211 node00757)))))) (add (add (add (add (add node00101 (add node01607 node00321)) (add (add (t Basis07.row583) (t Basis07.row584)) (add (t Basis07.row585) Basis07.row586))) (add (add (add node01459 (t Basis07.row590)) (add Basis07.row591 Basis07.row592)) (add (add node00829 node00905) (add Basis07.row598 (t Basis07.row598))))) (add (add (add (add node00276 (t Basis07.row601)) (add node00000 (t Basis07.row606))) (add (add node01031 (t Basis07.row610)) (add (t Basis07.row611) node00794))) (add (add (add node02321 Basis07.row616) (add (t Basis07.row616) Basis07.row619)) (add (add node03027 Basis07.row623) (add node02629 Basis07.row628))))) (add (add (add (add node04171 (add Basis07.row632 Basis07.row633)) (add (add node00469 node00904) (add (t Basis07.row639) Basis07.row640))) (add (add (add Basis07.row641 (t Basis07.row641)) (add node01095 node01963)) (add (add node00672 node01691) (add node00974 Basis07.row652)))) (add (add (add (add (t Basis07.row652) node03094) (add node00831 (t Basis07.row657))) (add (add (t Basis07.row658) (t Basis07.row661)) (add Basis07.row663 node00821))) (add (add (add node03392 (t Basis07.row668)) (add (t Basis07.row669) node00836)) (add (add node00373 node01626) (add node00886 node04073))))))) (add (add (add (add (add (add (t Basis07.row681) (add (t Basis07.row682) Basis07.row684)) (add (add (t Basis07.row684) (t Basis07.row686)) (add (t Basis07.row687) (t Basis07.row689)))) (add (add (add node02062 node00292) (add node03860 Basis07.row696)) (add (add (t Basis07.row698) (t Basis07.row701)) (add node01735 Basis07.row704)))) (add (add (add (add Basis07.row705 node00529) (add node03951 Basis07.row711)) (add (add Basis07.row712 (t Basis07.row713)) (add (t Basis07.row714) (t Basis07.row716)))) (add (add (add node01062 node02260) (add node03230 node01035)) (add (add node01904 node00278) (add node03269 node01867))))) (add (add (add (add node00887 (add node00216 node00451)) (add (add Basis07.row742 Basis07.row744) (add node01383 node01781))) (add (add (add Basis07.row749 (t Basis07.row749)) (add Basis07.row751 node01473)) (add (add node00988 node01980) (add Basis07.row759 Basis07.row760)))) (add (add (add (add node00797 node02200) (add node01492 Basis07.row767)) (add (add node01255 node01142) (add node04280 Basis07.row778))) (add (add (add Basis07.row779 Basis07.row780) (add node03783 Basis07.row784)) (add (add node00247 Basis07.row789) (add node02173 node00188)))))) (add (add (add (add (add node01203 (add node02526 node03566)) (add (add Basis07.row801 node00410) (add (t Basis07.row804) Basis07.row805))) (add (add (add (t Basis07.row807) node02879) (add (t Basis07.row810) (t Basis07.row812))) (add (add (t Basis07.row813) Basis07.row814) (add Basis07.row815 (t Basis07.row815))))) (add (add (add (add Basis07.row817 Basis07.row818) (add node00919 node00718)) (add (add (t Basis07.row825) (t Basis07.row827)) (add (t Basis07.row829) Basis07.row831))) (add (add (add (t Basis07.row832) (t Basis07.row833)) (add node00533 (t Basis07.row835))) (add (add Basis07.row838 (t Basis07.row839)) (add node01616 (t Basis07.row843)))))) (add (add (add (add Basis07.row844 (add Basis07.row845 node03037)) (add (add (t Basis07.row849) (t Basis07.row850)) (add Basis07.row851 (t Basis07.row854)))) (add (add (add node01221 (t Basis07.row856)) (add (t Basis07.row857) node02580)) (add (add node02019 node01119) (add node01574 (t Basis07.row867))))) (add (add (add (add node00941 node01590) (add node03996 node01788)) (add (add Basis07.row876 node00581) (add node01060 (t Basis07.row880)))) (add (add (add Basis07.row882 node01135) (add Basis07.row885 node03794)) (add (add Basis07.row888 (t Basis07.row889)) (add node00668 node02612)))))))))

private theorem row167 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 167 (0, 0)) ((rowsAt 10).getD 167 (0, 0)) := by
  apply of_certificate witness167
  · decide +kernel
  · decide +kernel

private noncomputable def witness168 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row046

private theorem row168 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 168 (0, 0)) ((rowsAt 10).getD 168 (0, 0)) := by
  apply of_certificate witness168
  · decide +kernel
  · decide +kernel

private noncomputable def witness169 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add (add Basis07.row001 (t Basis07.row001)) (add Basis07.row002 node01376)) (add (add Basis07.row005 node02818) (add Basis07.row012 node03360))) (add (add (add node04202 Basis07.row019) (add Basis07.row020 node04020)) (add (add node00817 node00559) (add Basis07.row028 (t Basis07.row028))))) (add (add (add (add Basis07.row029 Basis07.row031) (add (t Basis07.row032) (t Basis07.row033))) (add (add (t Basis07.row037) node04390) (add node00284 Basis07.row045))) (add (add (add node00115 Basis07.row048) (add (t Basis07.row049) node02599)) (add (add Basis07.row053 node02324) (add (t Basis07.row056) Basis07.row057))))) (add (add (add (add (add node02466 node01103) (add (t Basis07.row062) Basis07.row064)) (add (add Basis07.row065 Basis07.row066) (add Basis07.row067 node01326))) (add (add (add node00916 node02860) (add (t Basis07.row073) (t Basis07.row074))) (add (add node01008 (t Basis07.row076)) (add (t Basis07.row077) (t Basis07.row080))))) (add (add (add (add (t Basis07.row081) Basis07.row082) (add node02068 node03671)) (add (add Basis07.row089 node00511) (add node02225 Basis07.row093))) (add (add (add (t Basis07.row094) Basis07.row097) (add node02310 node01295)) (add (add node02093 Basis07.row104) (add Basis07.row105 Basis07.row107)))))) (add (add (add (add (add (add (t Basis07.row108) (t Basis07.row109)) (add Basis07.row110 node00806)) (add (add (t Basis07.row113) (t Basis07.row114)) (add Basis07.row116 node00948))) (add (add (add node02667 Basis07.row124) (add (t Basis07.row125) Basis07.row128)) (add (add (t Basis07.row128) node00075) (add node00457 Basis07.row134)))) (add (add (add (add (t Basis07.row135) (t Basis07.row136)) (add (t Basis07.row137) node02639)) (add (add Basis07.row143 (t Basis07.row144)) (add node01546 node00309))) (add (add (add (t Basis07.row148) node03514) (add node02393 node01646)) (add (add (t Basis07.row156) node03353) (add (t Basis07.row160) node00537))))) (add (add (add (add (add (t Basis07.row163) (t Basis07.row167)) (add node00045 Basis07.row172)) (add (add Basis07.row173 node00205) (add node00968 (t Basis07.row178)))) (add (add (add node02046 Basis07.row181) (add Basis07.row182 node03676)) (add (add Basis07.row185 Basis07.row186) (add node01238 node02067)))) (add (add (add (add node00833 node03756) (add node01363 node01766)) (add (add Basis07.row201 node00093) (add node04250 node00765))) (add (add (add node01633 node02205) (add Basis07.row214 Basis07.row215)) (add (add (t Basis07.row216) Basis07.row218) (add Basis07.row219 Basis07.row222))))))) (add (add (add (add (add (add (add Basis07.row223 (t Basis07.row224)) (add Basis07.row227 node03836)) (add (add node00663 node02228) (add node00709 (t Basis07.row239)))) (add (add (add (t Basis07.row240) Basis07.row241) (add node03371 Basis07.row244)) (add (add (t Basis07.row246) Basis07.row248) (add Basis07.row250 node00518)))) (add (add (add (add (t Basis07.row252) Basis07.row253) (add node02524 node03241)) (add (add node00679 (t Basis07.row262)) (add node01892 (t Basis07.row266)))) (add (add (add (t Basis07.row267) Basis07.row269) (add Basis07.row270 Basis07.row271)) (add (add node02512 (t Basis07.row274)) (add Basis07.row275 node00777))))) (add (add (add (add (add node00539 node01511) (add (t Basis07.row281) node03500)) (add (add (t Basis07.row286) (t Basis07.row288)) (add node01972 (t Basis07.row291)))) (add (add (add (t Basis07.row292) node01046) (add node01365 Basis07.row297)) (add (add (t Basis07.row297) (t Basis07.row299)) (add Basis07.row300 Basis07.row301)))) (add (add (add (add Basis07.row304 (t Basis07.row304)) (add Basis07.row306 node00225)) (add (add (t Basis07.row311) (t Basis07.row314)) (add node02772 node02938))) (add (add (add (t Basis07.row321) node01503) (add (t Basis07.row325) node03411)) (add (add node04098 Basis07.row332) (add node00651 Basis07.row336)))))) (add (add (add (add (add (add Basis07.row337 node01828) (add node00573 node01316)) (add (add (t Basis07.row344) (t Basis07.row345)) (add node00784 Basis07.row348))) (add (add (add Basis07.row349 node00762) (add node02596 (t Basis07.row354))) (add (add node02080 (t Basis07.row357)) (add node01521 Basis07.row363)))) (add (add (add (add Basis07.row366 node00845) (add (t Basis07.row369) (t Basis07.row370))) (add (add Basis07.row371 (t Basis07.row372)) (add node00048 node00444))) (add (add (add node03109 node01168) (add node02560 node04188)) (add (add (t Basis07.row386) node02427) (add node01048 (t Basis07.row392)))))) (add (add (add (add (add (t Basis07.row393) node00652) (add Basis07.row396 (t Basis07.row396))) (add (add Basis07.row399 Basis07.row400) (add Basis07.row403 node02131))) (add (add (add node00445 (t Basis07.row407)) (add node01280 Basis07.row411)) (add (add node01367 node03157) (add node00721 Basis07.row419)))) (add (add (add (add (t Basis07.row420) node00565) (add node03091 Basis07.row426)) (add (add Basis07.row427 node00613) (add Basis07.row431 (t Basis07.row432)))) (add (add (add node01030 (t Basis07.row435)) (add node00259 node00697)) (add (add (t Basis07.row443) (t Basis07.row445)) (add (t Basis07.row446) (t Basis07.row447))))))))) (add (add (add (add (add (add (add (add node00367 node02749) (add Basis07.row453 (t Basis07.row453))) (add (add (t Basis07.row454) node00260) (add (t Basis07.row457) node01960))) (add (add (add node01658 node00524) (add (t Basis07.row465) node02809)) (add (add node01093 (t Basis07.row470)) (add (t Basis07.row471) Basis07.row472)))) (add (add (add (add node02727 node00575) (add (t Basis07.row476) (t Basis07.row477))) (add (add node02002 node02216) (add node04353 Basis07.row486))) (add (add (add Basis07.row487 node01051) (add node03114 (t Basis07.row492))) (add (add Basis07.row493 node02527) (add Basis07.row498 node02294))))) (add (add (add (add (add Basis07.row502 node04165) (add node01985 node02844)) (add (add (t Basis07.row510) (t Basis07.row511)) (add Basis07.row512 Basis07.row513))) (add (add (add Basis07.row515 (t Basis07.row516)) (add node00799 node00870)) (add (add Basis07.row521 (t Basis07.row521)) (add node00897 Basis07.row526)))) (add (add (add (add (t Basis07.row526) (t Basis07.row528)) (add (t Basis07.row529) Basis07.row530)) (add (add node02720 node01196) (add Basis07.row536 Basis07.row538))) (add (add (add node01063 Basis07.row544) (add Basis07.row545 node00932)) (add (add Basis07.row550 (t Basis07.row553)) (add Basis07.row557 node00029)))))) (add (add (add (add (add (add (t Basis07.row560) node00466) (add node00787 Basis07.row565)) (add (add (t Basis07.row565) node00157) (add Basis07.row569 node01734))) (add (add (add node02522 node00898) (add node02039 Basis07.row580)) (add (add node02072 node00682) (add Basis07.row586 node01429)))) (add (add (add (add (t Basis07.row591) Basis07.row592) (add node00810 (t Basis07.row595))) (add (add node01330 node00935) (add (t Basis07.row603) Basis07.row605))) (add (add (add Basis07.row606 (t Basis07.row606)) (add Basis07.row607 node02258)) (add (add node00467 Basis07.row617) (add node00060 (t Basis07.row622)))))) (add (add (add (add (add Basis07.row624 node04315) (add Basis07.row628 Basis07.row629)) (add (add Basis07.row630 (t Basis07.row631)) (add node01844 node01369))) (add (add (add (t Basis07.row637) node00405) (add Basis07.row640 node02322)) (add (add Basis07.row644 Basis07.row646) (add Basis07.row647 (t Basis07.row647))))) (add (add (add (add Basis07.row648 Basis07.row649) (add Basis07.row652 node01778)) (add (add node00577 (t Basis07.row657)) (add Basis07.row660 node01018))) (add (add (add Basis07.row663 (t Basis07.row663)) (add node03029 (t Basis07.row667))) (add (add node01345 Basis07.row670) (add node01543 node00246))))))) (add (add (add (add (add (add (add node00917 node01079) (add Basis07.row680 (t Basis07.row680))) (add (add Basis07.row682 node03394) (add (t Basis07.row686) (t Basis07.row687)))) (add (add (add node03627 node01666) (add node03542 node01489)) (add (add node01229 node00186) (add (t Basis07.row700) node01735)))) (add (add (add (add node01927 (t Basis07.row707)) (add Basis07.row708 (t Basis07.row708))) (add (add node02647 node00187) (add Basis07.row715 (t Basis07.row716)))) (add (add (add node03399 Basis07.row719) (add node02339 node03230)) (add (add (t Basis07.row725) (t Basis07.row726)) (add node02542 (t Basis07.row729)))))) (add (add (add (add (add node01099 Basis07.row733) (add node00375 (t Basis07.row736))) (add (add node02301 node02498) (add node00294 (t Basis07.row745)))) (add (add (add node02564 Basis07.row749) (add Basis07.row750 node00508)) (add (add node00673 node01473) (add Basis07.row756 (t Basis07.row756))))) (add (add (add (add node01980 node02994) (add Basis07.row762 (t Basis07.row762))) (add (add node01577 node02421) (add node01748 node01733))) (add (add (add Basis07.row771 node03743) (add node02861 node00984)) (add (add node00711 Basis07.row781) (add Basis07.row782 node00735)))))) (add (add (add (add (add (add (t Basis07.row787) node01248) (add node02015 (t Basis07.row793))) (add (add node04265 Basis07.row797) (add node00743 node00580))) (add (add (add node01784 (t Basis07.row804)) (add Basis07.row805 node04194)) (add (add Basis07.row809 Basis07.row810) (add node02017 node00878)))) (add (add (add (add Basis07.row815 Basis07.row816) (add Basis07.row817 (t Basis07.row817))) (add (add node01109 Basis07.row820) (add node02069 node03699))) (add (add (add (t Basis07.row826) (t Basis07.row827)) (add Basis07.row828 node03993)) (add (add node00494 node01910) (add node04273 Basis07.row838))))) (add (add (add (add (add (t Basis07.row840) node02471) (add node00043 Basis07.row845)) (add (add Basis07.row846 node01672) (add node02124 (t Basis07.row851)))) (add (add (add (t Basis07.row852) node00623) (add node04291 (t Basis07.row858))) (add (add Basis07.row859 node02621) (add Basis07.row864 node00203)))) (add (add (add (add node02759 Basis07.row868) (add node02204 node00204)) (add (add node00646 (t Basis07.row877)) (add Basis07.row879 Basis07.row880))) (add (add (add node00248 (t Basis07.row883)) (add (t Basis07.row884) node00605)) (add (add (t Basis07.row887) Basis07.row888) (add (t Basis07.row889) (add node00235 node00169))))))))))

private theorem row169 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 169 (0, 0)) ((rowsAt 10).getD 169 (0, 0)) := by
  apply of_certificate witness169
  · decide +kernel
  · decide +kernel

private noncomputable def witness170 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row404

private theorem row170 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 170 (0, 0)) ((rowsAt 10).getD 170 (0, 0)) := by
  apply of_certificate witness170
  · decide +kernel
  · decide +kernel

private noncomputable def witness171 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add node02930 (add (t Basis07.row004) node01102)) (add (add node03246 Basis07.row010) (add node03149 (t Basis07.row013)))) (add (add Basis07.row016 (add Basis07.row018 node00114)) (add (add (t Basis07.row020) (t Basis07.row022)) (add Basis07.row023 node03727)))) (add (add (add (t Basis07.row026) (add node00866 node02661)) (add (add node00307 node01408) (add node00991 node01497))) (add (add (add Basis07.row039 Basis07.row040) (add node02357 node00115)) (add (add node00626 node00357) (add (t Basis07.row051) (t Basis07.row053)))))) (add (add (add (add node02666 (add node00072 node01700)) (add (add node03291 Basis07.row062) (add (t Basis07.row063) (t Basis07.row065)))) (add (add (add Basis07.row066 node00001) (add node02368 node02442)) (add (add (t Basis07.row074) node01008) (add node02954 Basis07.row080)))) (add (add (add Basis07.row083 (add Basis07.row084 (t Basis07.row085))) (add (add Basis07.row089 node01021) (add node01307 Basis07.row098))) (add (add (add Basis07.row099 (t Basis07.row099)) (add (t Basis07.row101) node02406)) (add (add (t Basis07.row104) node03648) (add (t Basis07.row109) node00627)))))) (add (add (add (add (add node04473 (add (t Basis07.row115) Basis07.row117)) (add (add node03512 node01386) (add node00840 Basis07.row125))) (add (add node00298 (add (t Basis07.row128) node03672)) (add (add node00847 (t Basis07.row134)) (add node01113 (t Basis07.row138))))) (add (add (add (t Basis07.row139) (add Basis07.row143 (t Basis07.row143))) (add (add node00515 node02433) (add (t Basis07.row148) Basis07.row149))) (add (add (add Basis07.row150 (t Basis07.row150)) (add (t Basis07.row152) (t Basis07.row153))) (add (add Basis07.row155 node02974) (add Basis07.row159 (t Basis07.row159)))))) (add (add (add (add node03516 (add node03284 (t Basis07.row166))) (add (add (t Basis07.row167) Basis07.row168) (add node04182 (t Basis07.row171)))) (add (add (add (t Basis07.row175) node02463) (add (t Basis07.row179) node00239)) (add (add node00181 (t Basis07.row185)) (add node03175 node02021)))) (add (add (add (t Basis07.row191) (add (t Basis07.row193) (t Basis07.row194))) (add (add Basis07.row196 (t Basis07.row197)) (add (t Basis07.row198) node01136))) (add (add (add node03296 node00826) (add node01291 node02482)) (add (add Basis07.row210 Basis07.row211) (add Basis07.row213 node03664))))))) (add (add (add (add (add (add node02978 (add Basis07.row219 Basis07.row220)) (add (add node01388 Basis07.row223) (add Basis07.row224 node03278))) (add (add node04403 (add node01751 node01707)) (add (add Basis07.row236 Basis07.row237) (add Basis07.row238 node02468)))) (add (add (add Basis07.row241 (add node00499 node01994)) (add (add Basis07.row247 node04345) (add node02748 (t Basis07.row255)))) (add (add (add node01027 (t Basis07.row259)) (add Basis07.row260 (t Basis07.row260))) (add (add node00366 Basis07.row265) (add node00254 node00638))))) (add (add (add (add (t Basis07.row273) (add node00272 node01028)) (add (add (t Basis07.row278) node02604) (add node03133 (t Basis07.row287)))) (add (add (add node00096 node01537) (add (t Basis07.row293) Basis07.row295)) (add (add Basis07.row296 node03838) (add node03487 node01932)))) (add (add (add node02285 (add Basis07.row309 Basis07.row311)) (add (add node03198 Basis07.row316) (add Basis07.row318 Basis07.row319))) (add (add (add node00172 (t Basis07.row321)) (add node03760 node00273)) (add (add node02230 node00120) (add node00152 Basis07.row340)))))) (add (add (add (add (add node01520 (add node01309 node01177)) (add (add node01829 Basis07.row350) (add Basis07.row352 (t Basis07.row352)))) (add (add (t Basis07.row353) (add node01415 node00077)) (add (add node01878 node00844) (add node01029 node03494)))) (add (add (add (t Basis07.row367) (add node00482 node02288)) (add (add node02567 Basis07.row374) (add Basis07.row377 node03109))) (add (add (add Basis07.row381 node01353) (add node04188 node00981)) (add (add Basis07.row389 (t Basis07.row389)) (add (t Basis07.row392) Basis07.row394))))) (add (add (add (add node02028 (add (t Basis07.row397) Basis07.row400)) (add (add node02055 Basis07.row405) (add (t Basis07.row405) Basis07.row408))) (add (add (add node02490 node02188) (add node00337 node01454)) (add (add node01832 node02800) (add Basis07.row421 (t Basis07.row423))))) (add (add (add Basis07.row424 (add (t Basis07.row425) Basis07.row426)) (add (add Basis07.row428 Basis07.row429) (add Basis07.row430 Basis07.row434))) (add (add (add node04136 Basis07.row440) (add (t Basis07.row441) node03529)) (add (add node00428 Basis07.row448) (add (t Basis07.row448) node03346)))))))) (add (add (add (add (add (add (add node01106 (add node00710 Basis07.row456)) (add (add node03381 (t Basis07.row460)) (add Basis07.row461 node01508))) (add (add (t Basis07.row466) (add node00340 node01194)) (add (add (t Basis07.row470) node01209) (add (t Basis07.row473) (t Basis07.row474))))) (add (add (add node00884 (add node02074 node00341)) (add (add Basis07.row482 node02939) (add node02576 node00615))) (add (add (add node00486 node01069) (add (t Basis07.row491) Basis07.row493)) (add (add node00318 node02170) (add node02293 node01354))))) (add (add (add (add (t Basis07.row504) (add Basis07.row505 node02581)) (add (add (t Basis07.row508) (t Basis07.row509)) (add node00588 Basis07.row513))) (add (add (add node02350 Basis07.row517) (add (t Basis07.row517) node00870)) (add (add Basis07.row522 node01155) (add node04347 Basis07.row527)))) (add (add (add node01802 (add node00156 (t Basis07.row532))) (add (add node04087 node02311) (add node03063 node01063))) (add (add (add node02110 node00853) (add node00165 (t Basis07.row553))) (add (add node01289 node02163) (add node04069 Basis07.row563)))))) (add (add (add (add (add (t Basis07.row563) (add node00732 (t Basis07.row566))) (add (add (t Basis07.row569) node00644) (add (t Basis07.row573) node03211))) (add (add node02039 (add Basis07.row580 Basis07.row581)) (add (add node01842 node01642) (add (t Basis07.row586) (t Basis07.row587))))) (add (add (add Basis07.row588 (add node00800 Basis07.row594)) (add (add (t Basis07.row594) node02724) (add Basis07.row600 Basis07.row601))) (add (add (add (t Basis07.row601) Basis07.row604) (add (t Basis07.row607) Basis07.row608)) (add (add node04002 Basis07.row612) (add node02562 (t Basis07.row618)))))) (add (add (add (add Basis07.row619 (add (t Basis07.row620) (t Basis07.row621))) (add (add node04093 node02992) (add node01466 node01191))) (add (add (add Basis07.row631 node00384) (add (t Basis07.row634) node02395)) (add (add node04072 (t Basis07.row643)) (add Basis07.row644 node00127)))) (add (add (add node00231 (add node02061 (t Basis07.row653))) (add (add node02916 (t Basis07.row657)) (add node02775 node00928))) (add (add (add node00433 (t Basis07.row664)) (add node02741 node03314)) (add (add Basis07.row671 node01632) (add node01975 Basis07.row676))))))) (add (add (add (add (add (add node00213 (add node03333 node00348)) (add (add node03119 node01461) (add node04168 node01724))) (add (add Basis07.row694 (add (t Basis07.row695) node02063)) (add (add (t Basis07.row698) node01173) (add Basis07.row703 Basis07.row704)))) (add (add (add node02199 (add (t Basis07.row707) Basis07.row708)) (add (add Basis07.row709 (t Basis07.row709)) (add node00293 node01740))) (add (add (add node02174 (t Basis07.row717)) (add Basis07.row722 Basis07.row723)) (add (add Basis07.row724 node00801) (add node00233 node02120))))) (add (add (add (add node00620 (add (t Basis07.row731) node00061)) (add (add node01057 Basis07.row742) (add Basis07.row744 (t Basis07.row744)))) (add (add (add (t Basis07.row746) node00296) (add (t Basis07.row750) (t Basis07.row751))) (add (add node03697 Basis07.row756) (add (t Basis07.row756) node01782)))) (add (add (add node00452 (add (t Basis07.row760) node00797)) (add (add (t Basis07.row764) Basis07.row765) (add node00387 Basis07.row769))) (add (add (add Basis07.row770 Basis07.row771) (add Basis07.row772 node01613)) (add (add node02014 node03732) (add node02023 node01424)))))) (add (add (add (add (add node00390 (add Basis07.row790 Basis07.row791)) (add (add (t Basis07.row793) node02961) (add node00925 node02894))) (add (add (t Basis07.row802) (add (t Basis07.row803) (t Basis07.row805))) (add (add node03784 node01001) (add (t Basis07.row811) Basis07.row812)))) (add (add (add Basis07.row813 (add node02672 node02250)) (add (add (t Basis07.row818) node03218) (add node00202 node02344))) (add (add (add (t Basis07.row825) node00888) (add Basis07.row831 node04348)) (add (add Basis07.row837 (t Basis07.row838)) (add (t Basis07.row839) Basis07.row840))))) (add (add (add (add node02356 (add (t Basis07.row843) node01871)) (add (add node03704 node02203) (add node00413 node02704))) (add (add (add node03548 node03466) (add (t Basis07.row860) (t Basis07.row861))) (add (add node03280 Basis07.row865) (add (t Basis07.row868) Basis07.row869)))) (add (add (add node01532 (add Basis07.row873 (t Basis07.row873))) (add (add Basis07.row874 Basis07.row875) (add node00331 (t Basis07.row877)))) (add (add (add node01198 node04019) (add node00455 Basis07.row886)) (add (add Basis07.row888 node02253) (add Basis07.row893 node00647)))))))))

private theorem row171 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 171 (0, 0)) ((rowsAt 10).getD 171 (0, 0)) := by
  apply of_certificate witness171
  · decide +kernel
  · decide +kernel

private noncomputable def witness172 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row409

private theorem row172 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 172 (0, 0)) ((rowsAt 10).getD 172 (0, 0)) := by
  apply of_certificate witness172
  · decide +kernel
  · decide +kernel

private noncomputable def witness173 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add node02678 (add Basis07.row002 node01535)) (add (add node00606 node00236) (add (t Basis07.row007) Basis07.row010))) (add (add (add node01144 Basis07.row014) (add node01741 Basis07.row018)) (add (add Basis07.row019 Basis07.row021) (add (t Basis07.row021) node01593)))) (add (add (add (add Basis07.row024 node00559) (add node00818 Basis07.row031)) (add (add (t Basis07.row032) Basis07.row033) (add Basis07.row035 node04368))) (add (add (add Basis07.row039 node00333) (add node02034 (t Basis07.row046))) (add (add node01549 Basis07.row049) (add (t Basis07.row050) node01758))))) (add (add (add (add (add Basis07.row057 Basis07.row058) (add node03511 Basis07.row063)) (add (add Basis07.row064 node01887) (add node01856 node04080))) (add (add (add node00269 (t Basis07.row075)) (add Basis07.row076 node00609)) (add (add node03975 (t Basis07.row081)) (add Basis07.row082 (t Basis07.row084))))) (add (add (add (add node04041 node01544) (add Basis07.row090 node02583)) (add (add Basis07.row093 (t Basis07.row094)) (add node02636 node02369))) (add (add (add Basis07.row101 Basis07.row102) (add Basis07.row103 Basis07.row104)) (add (add node00044 (t Basis07.row106)) (add Basis07.row108 node02674)))))) (add (add (add (add (add node00806 (add node00478 (t Basis07.row117))) (add (add node00363 Basis07.row120) (add Basis07.row121 node02973))) (add (add (add node00945 node02623) (add node01550 (t Basis07.row129))) (add (add Basis07.row130 Basis07.row132) (add node02826 node00497)))) (add (add (add (add Basis07.row140 Basis07.row144) (add node00438 (t Basis07.row147))) (add (add node01065 node01761) (add node02183 node01515))) (add (add (add node00768 node00299) (add (t Basis07.row158) node00018)) (add (add node00537 node00950) (add node04469 Basis07.row167))))) (add (add (add (add (add node03702 node02045) (add node01468 (t Basis07.row175))) (add (add Basis07.row176 node01823) (add (t Basis07.row181) (t Basis07.row182)))) (add (add (add Basis07.row183 (t Basis07.row184)) (add node01692 Basis07.row188)) (add (add node01705 (t Basis07.row190)) (add Basis07.row191 node01437)))) (add (add (add (add Basis07.row194 (t Basis07.row195)) (add Basis07.row196 Basis07.row197)) (add (add Basis07.row198 node03911) (add Basis07.row202 node01387))) (add (add (add (t Basis07.row204) node01599) (add (t Basis07.row208) (t Basis07.row210))) (add (add Basis07.row214 Basis07.row215) (add (t Basis07.row216) node01452))))))) (add (add (add (add (add (add Basis07.row220 (add Basis07.row221 Basis07.row222)) (add (add Basis07.row223 node00804) (add (t Basis07.row226) (t Basis07.row227)))) (add (add (add Basis07.row230 (t Basis07.row230)) (add (t Basis07.row231) node03104)) (add (add node01869 Basis07.row237) (add (t Basis07.row240) node01025)))) (add (add (add (add Basis07.row243 node00148) (add node01517 Basis07.row249)) (add (add Basis07.row250 node00518) (add (t Basis07.row252) (t Basis07.row253)))) (add (add (add (t Basis07.row254) Basis07.row256) (add node02795 Basis07.row259)) (add (add node02050 (t Basis07.row262)) (add Basis07.row265 (t Basis07.row265)))))) (add (add (add (add (add node03254 node01794) (add Basis07.row272 node01028)) (add (add node02796 Basis07.row280) (add Basis07.row281 node01011))) (add (add (add (t Basis07.row283) (t Basis07.row286)) (add (t Basis07.row287) (t Basis07.row288))) (add (add (t Basis07.row289) (t Basis07.row290)) (add node00311 node00664)))) (add (add (add (add node03226 Basis07.row300) (add Basis07.row301 node00792)) (add (add node00399 node03619) (add node02361 node00443))) (add (add (add node00867 node00243) (add Basis07.row318 (t Basis07.row318))) (add (add (t Basis07.row319) (t Basis07.row320)) (add node00859 node03666)))))) (add (add (add (add (add (add (t Basis07.row326) node02148) (add (t Basis07.row332) node03375)) (add (add (t Basis07.row336) Basis07.row337) (add (t Basis07.row339) (t Basis07.row340)))) (add (add (add Basis07.row341 node01520) (add node02663 Basis07.row347)) (add (add node01935 node00762) (add (t Basis07.row351) Basis07.row352)))) (add (add (add (add node03108 Basis07.row355) (add Basis07.row357 node01956)) (add (add node01521 node01214) (add (t Basis07.row365) (t Basis07.row366)))) (add (add (add Basis07.row367 (t Basis07.row368)) (add Basis07.row369 node01688)) (add (add (t Basis07.row373) Basis07.row374) (add node00038 node01083))))) (add (add (add (add (add Basis07.row379 Basis07.row380) (add (t Basis07.row380) (t Basis07.row383))) (add (add Basis07.row384 Basis07.row387) (add node02427 node01049))) (add (add (add node01999 node03110) (add (t Basis07.row395) node03449)) (add (add Basis07.row400 node03843) (add Basis07.row404 (t Basis07.row405))))) (add (add (add (add Basis07.row408 node01377) (add (t Basis07.row410) node00337)) (add (add (t Basis07.row414) (t Basis07.row415)) (add node03438 node01753))) (add (add (add Basis07.row423 node00313) (add Basis07.row427 Basis07.row429)) (add (add node00338 node00484) (add node00586 node00314)))))))) (add (add (add (add (add (add (add node00027 (add (t Basis07.row439) (t Basis07.row441))) (add (add node02106 node01399) (add (t Basis07.row447) Basis07.row449))) (add (add (add Basis07.row451 (t Basis07.row452)) (add node02056 node02001)) (add (add node00068 node01390) (add node02266 node04064)))) (add (add (add (add (t Basis07.row466) (t Basis07.row468)) (add node01194 (t Basis07.row472))) (add (add node01440 Basis07.row476) (add (t Basis07.row476) (t Basis07.row477)))) (add (add (add node00341 node00738) (add (t Basis07.row481) node01107)) (add (add node01863 node01137) (add node00824 Basis07.row492))))) (add (add (add (add (add Basis07.row493 (t Basis07.row493)) (add node01660 node00616)) (add (add Basis07.row499 node00447) (add Basis07.row502 node02435))) (add (add (add node00429 Basis07.row506) (add Basis07.row507 (t Basis07.row508))) (add (add node02874 Basis07.row511) (add node01628 (t Basis07.row516))))) (add (add (add (add Basis07.row517 node01188) (add node00870 node01268)) (add (add (t Basis07.row522) Basis07.row527) (add (t Basis07.row527) node01872))) (add (add (add node01281 node04446) (add Basis07.row536 Basis07.row538)) (add (add node04117 Basis07.row542) (add (t Basis07.row542) node02540)))))) (add (add (add (add (add (add (t Basis07.row546) Basis07.row547) (add Basis07.row548 node01053)) (add (add (t Basis07.row553) Basis07.row555) (add node00933 node02112))) (add (add (add node02940 node00787) (add Basis07.row565 Basis07.row567)) (add (add node04144 Basis07.row571) (add Basis07.row573 node00972)))) (add (add (add (add (t Basis07.row577) Basis07.row579) (add Basis07.row582 (t Basis07.row582))) (add (add node02235 node01429) (add Basis07.row589 (t Basis07.row589)))) (add (add (add (t Basis07.row590) Basis07.row592) (add node00872 node01116)) (add (add node03850 node01330) (add (t Basis07.row601) node00344))))) (add (add (add (add (add node01814 node02193) (add (t Basis07.row610) Basis07.row611)) (add (add Basis07.row612 (t Basis07.row612)) (add Basis07.row615 (t Basis07.row615)))) (add (add (add Basis07.row618 Basis07.row620) (add (t Basis07.row620) node00007)) (add (add Basis07.row626 (t Basis07.row627)) (add (t Basis07.row630) Basis07.row631)))) (add (add (add (add (t Basis07.row632) (t Basis07.row633)) (add Basis07.row634 (t Basis07.row634))) (add (add node03457 node01983) (add node03391 Basis07.row643))) (add (add (add node00127 Basis07.row647) (add (t Basis07.row647) Basis07.row648)) (add (add Basis07.row649 Basis07.row651) (add (t Basis07.row654) node02916))))))) (add (add (add (add (add (add (t Basis07.row657) (add node02563 node00433)) (add (add node03029 node00506) (add (t Basis07.row668) Basis07.row672))) (add (add (add Basis07.row673 (t Basis07.row676)) (add Basis07.row678 node02943)) (add (add node01496 node03394) (add (t Basis07.row686) Basis07.row687)))) (add (add (add (add node02855 node02062) (add Basis07.row693 (t Basis07.row693))) (add (add Basis07.row695 node01489) (add (t Basis07.row698) (t Basis07.row699)))) (add (add (add Basis07.row702 Basis07.row703) (add Basis07.row704 (t Basis07.row706))) (add (add node00929 Basis07.row709) (add node01625 (t Basis07.row715)))))) (add (add (add (add (add Basis07.row716 (t Basis07.row718)) (add (t Basis07.row719) node01299)) (add (add node00492 Basis07.row725) (add node03165 node00325))) (add (add (add node01904 Basis07.row731) (add (t Basis07.row731) Basis07.row732)) (add (add node01875 (t Basis07.row737)) (add node04367 Basis07.row742)))) (add (add (add (add Basis07.row743 (t Basis07.row743)) (add node01495 node00263)) (add (add node02549 Basis07.row756) (add (t Basis07.row756) node01980))) (add (add (add node03217 (t Basis07.row761)) (add Basis07.row763 (t Basis07.row765))) (add (add node02161 (t Basis07.row769)) (add node02839 Basis07.row776)))))) (add (add (add (add (add (add Basis07.row777 node00409) (add node03336 node01907)) (add (add Basis07.row786 Basis07.row787) (add node00063 (t Basis07.row791)))) (add (add (add (t Basis07.row792) Basis07.row793) (add node03565 node02526)) (add (add node01170 node03806) (add node00410 Basis07.row804)))) (add (add (add (add node04194 node01001) (add Basis07.row811 (t Basis07.row813))) (add (add Basis07.row814 node01687) (add Basis07.row818 node00659))) (add (add (add Basis07.row821 node02069) (add node03939 node00888)) (add (add node02065 (t Basis07.row830)) (add node00958 Basis07.row835))))) (add (add (add (add (add Basis07.row836 (t Basis07.row836)) (add Basis07.row837 (t Basis07.row839))) (add (add (t Basis07.row841) node00975) (add (t Basis07.row844) node00020))) (add (add (add node00645 (t Basis07.row851)) (add Basis07.row852 node04155)) (add (add node03047 node02621) (add Basis07.row863 node00474)))) (add (add (add (add node00203 node01500) (add Basis07.row870 node01787)) (add (add (t Basis07.row873) Basis07.row874) (add Basis07.row875 (t Basis07.row876)))) (add (add (add node03578 Basis07.row881) (add node03281 Basis07.row885)) (add (add node02272 node02423) (add node02603 node03136)))))))))

private theorem row173 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 173 (0, 0)) ((rowsAt 10).getD 173 (0, 0)) := by
  apply of_certificate witness173
  · decide +kernel
  · decide +kernel

private noncomputable def witness174 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add node01884 (add (t Basis07.row003) node00606)) (add (add Basis07.row008 (t Basis07.row011)) (add node01447 node02680))) (add (add (add node01206 Basis07.row018) (add node00114 (t Basis07.row020))) (add (add (t Basis07.row022) node02273) (add (t Basis07.row025) node03290)))) (add (add (add (add Basis07.row031 Basis07.row033) (add node00266 node00991)) (add (add node04122 node01111) (add Basis07.row042 Basis07.row043))) (add (add (add Basis07.row044 node03553) (add node00026 node02211)) (add (add node00456 (t Basis07.row054)) (add Basis07.row056 node01578))))) (add (add (add (add node00116 (add Basis07.row061 Basis07.row062)) (add (add node00391 node03902) (add Basis07.row069 Basis07.row071))) (add (add (add Basis07.row072 node04297) (add node00662 node01923)) (add (add node00191 node00134) (add node02274 node00308)))) (add (add (add (add node03137 Basis07.row089) (add node01021 node01406)) (add (add Basis07.row094 node01307) (add node00074 node00496))) (add (add (add node01934 (t Basis07.row106)) (add Basis07.row108 Basis07.row109)) (add (add node02771 node00806) (add Basis07.row115 Basis07.row116)))))) (add (add (add (add (add node00948 (add node01112 (t Basis07.row120))) (add (add node01242 node01043) (add node00945 node02648))) (add (add (add node00649 node01584) (add (t Basis07.row135) node00909)) (add (add (t Basis07.row137) node00028) (add (t Basis07.row143) Basis07.row145)))) (add (add (add (add node02751 (t Basis07.row149)) (add node02279 Basis07.row152)) (add (add Basis07.row153 node01762) (add Basis07.row157 (t Basis07.row158)))) (add (add (add node00780 node00537) (add node00092 node00180)) (add (add node01226 Basis07.row168) (add node01553 (t Basis07.row172)))))) (add (add (add (add node02307 (add node00334 node03171)) (add (add node00239 node02425) (add (t Basis07.row184) Basis07.row185))) (add (add (add Basis07.row188 (t Basis07.row188)) (add node03979 node03756)) (add (add node00708 node02432) (add node03331 Basis07.row202)))) (add (add (add (add (t Basis07.row202) (t Basis07.row203)) (add Basis07.row204 (t Basis07.row205))) (add (add (t Basis07.row206) node00393) (add node00394 node01621))) (add (add (add node00538 Basis07.row216) (add (t Basis07.row217) (t Basis07.row220))) (add (add node01824 node00094) (add node02929 node02430))))))) (add (add (add (add (add (add node02824 (add node02869 node01708)) (add (add Basis07.row241 node00499) (add (t Basis07.row244) (t Basis07.row245)))) (add (add (add Basis07.row246 node00769) (add node03804 (t Basis07.row252))) (add (add (t Basis07.row253) (t Basis07.row254)) (add Basis07.row255 node01154)))) (add (add (add (add node00812 node03000) (add node03959 node01815)) (add (add (t Basis07.row268) (t Basis07.row271)) (add Basis07.row272 (t Basis07.row274)))) (add (add (add Basis07.row276 (t Basis07.row277)) (add (t Basis07.row279) (t Basis07.row280))) (add (add Basis07.row282 (t Basis07.row284)) (add node00540 node00694))))) (add (add (add (add (t Basis07.row289) (add (t Basis07.row290) Basis07.row293)) (add (add (t Basis07.row293) node02590) (add (t Basis07.row296) node03838))) (add (add (add node01288 (t Basis07.row303)) (add Basis07.row306 node01768)) (add (add node02255 node00443) (add node00867 Basis07.row317)))) (add (add (add (add (t Basis07.row318) node03863) (add node01084 node02538)) (add (add node00015 node01213) (add node00883 node03918))) (add (add (add node02207 node00120) (add node00995 node04214)) (add (add node00542 node02735) (add node01309 Basis07.row346)))))) (add (add (add (add (add (t Basis07.row346) (add Basis07.row348 node02287)) (add (add node00109 node00244) (add (t Basis07.row354) Basis07.row355))) (add (add (add (t Basis07.row356) (t Basis07.row358)) (add (t Basis07.row359) node00844)) (add (add (t Basis07.row362) Basis07.row365) (add (t Basis07.row366) node02505)))) (add (add (add (add node02262 node02896) (add node00048 (t Basis07.row375))) (add (add (t Basis07.row378) Basis07.row379) (add Basis07.row380 (t Basis07.row382)))) (add (add (add node01068 (t Basis07.row386)) (add node02427 node03134)) (add (add node04216 Basis07.row396) (add Basis07.row397 node03203))))) (add (add (add (add node01252 (add node00425 node02472)) (add (add Basis07.row409 Basis07.row410) (add node01679 (t Basis07.row412)))) (add (add (add node02922 node01321) (add Basis07.row419 node01510)) (add (add Basis07.row424 node01114) (add (t Basis07.row428) (t Basis07.row429))))) (add (add (add (add node00338 Basis07.row433) (add Basis07.row435 Basis07.row436)) (add (add node02999 Basis07.row439) (add Basis07.row441 (t Basis07.row441)))) (add (add (add node03529 node01689) (add (t Basis07.row447) Basis07.row449)) (add (add Basis07.row450 Basis07.row451) (add node00931 node00710)))))))) (add (add (add (add (add (add (add (t Basis07.row458) (add Basis07.row459 Basis07.row463)) (add (add Basis07.row464 node01212) (add node00340 node01194))) (add (add (add node04346 node01440) (add node00997 node00317)) (add (add Basis07.row480 node00791) (add Basis07.row485 Basis07.row486)))) (add (add (add (add Basis07.row489 (t Basis07.row489)) (add (t Basis07.row490) Basis07.row492)) (add (add node02547 node02107) (add node00110 node00447))) (add (add (add node00370 node04377) (add node01276 (t Basis07.row508))) (add (add (t Basis07.row510) node01311) (add node00174 Basis07.row515))))) (add (add (add (add (t Basis07.row516) (add node03742 Basis07.row521)) (add (add Basis07.row522 (t Basis07.row522)) (add Basis07.row523 node03049))) (add (add (add node00100 node00261) (add (t Basis07.row530) Basis07.row532)) (add (add Basis07.row533 Basis07.row534) (add Basis07.row536 Basis07.row537)))) (add (add (add (add node01312 node01108) (add Basis07.row542 node00741)) (add (add Basis07.row545 (t Basis07.row545)) (add (t Basis07.row546) node00195))) (add (add (add node00983 node01974) (add (t Basis07.row553) (t Basis07.row554))) (add (add node03135 Basis07.row559) (add node01054 Basis07.row561)))))) (add (add (add (add (add Basis07.row565 (add (t Basis07.row565) node01962)) (add (add node00196 Basis07.row572) (add node02522 node03881))) (add (add (add (t Basis07.row578) node00846) (add (t Basis07.row580) node00321)) (add (add node02528 Basis07.row586) (add node01459 node00800)))) (add (add (add (add node00212 (t Basis07.row593)) (add Basis07.row596 Basis07.row597)) (add (add Basis07.row598 (t Basis07.row598)) (add (t Basis07.row599) Basis07.row600))) (add (add (add node01189 (t Basis07.row602)) (add node02439 Basis07.row609)) (add (add (t Basis07.row610) (t Basis07.row611)) (add Basis07.row612 (t Basis07.row612)))))) (add (add (add (add node02562 (add node02691 (t Basis07.row619))) (add (add Basis07.row620 node04313) (add node02117 (t Basis07.row625)))) (add (add (add node02206 (t Basis07.row631)) (add (t Basis07.row632) Basis07.row633)) (add (add node03028 Basis07.row637) (add Basis07.row640 node01095)))) (add (add (add (add node01686 node01032) (add node00231 node03642)) (add (add (t Basis07.row652) node01096) (add (t Basis07.row655) Basis07.row656))) (add (add (add Basis07.row658 node00346) (add (t Basis07.row661) Basis07.row663)) (add (add node00821 Basis07.row666) (add Basis07.row667 node01964))))))) (add (add (add (add (add (add node01139 (add node01270 Basis07.row675)) (add (add node00917 (t Basis07.row680)) (add node01750 node00008))) (add (add (add node00292 (t Basis07.row693)) (add Basis07.row695 (t Basis07.row696))) (add (add Basis07.row697 Basis07.row698) (add Basis07.row700 Basis07.row701)))) (add (add (add (add node02390 node01848) (add (t Basis07.row706) node02158)) (add (add Basis07.row710 node01901) (add node01625 node02174))) (add (add (add Basis07.row717 node03358) (add node01439 node04285)) (add (add (t Basis07.row728) node01694) (add node03273 Basis07.row734))))) (add (add (add (add Basis07.row735 (add node00061 node01380)) (add (add node03963 (t Basis07.row742)) (add node03123 (t Basis07.row745)))) (add (add (add node02564 Basis07.row749) (add (t Basis07.row749) node01905)) (add (add node00673 node02383) (add Basis07.row757 Basis07.row759)))) (add (add (add (add node03462 (t Basis07.row762)) (add node01680 Basis07.row766)) (add (add node02077 node01733) (add (t Basis07.row771) Basis07.row773))) (add (add (add (t Basis07.row773) node03782) (add node02790 Basis07.row780)) (add (add (t Basis07.row780) (t Basis07.row782)) (add (t Basis07.row783) Basis07.row787)))))) (add (add (add (add (add Basis07.row789 (add node02386 (t Basis07.row792))) (add (add node01909 Basis07.row795) (add node01404 (t Basis07.row798)))) (add (add (add (t Basis07.row800) Basis07.row801) (add node00410 (t Basis07.row805))) (add (add node00234 node04235) (add Basis07.row811 Basis07.row814)))) (add (add (add (add node02672 node01509) (add (t Basis07.row819) Basis07.row821)) (add (add Basis07.row822 Basis07.row823) (add node00079 node03011))) (add (add (add (t Basis07.row827) Basis07.row828) (add (t Basis07.row828) (t Basis07.row829))) (add (add Basis07.row831 node03084) (add node03125 node00354))))) (add (add (add (add (add node01682 Basis07.row842) (add Basis07.row844 node02261)) (add (add node00020 node01630) (add Basis07.row851 node00623))) (add (add (add node01673 (t Basis07.row857)) (add Basis07.row858 (t Basis07.row860))) (add (add node04433 node02759) (add node00176 node00569)))) (add (add (add (add Basis07.row872 Basis07.row873) (add node02545 Basis07.row878)) (add (add (t Basis07.row878) (t Basis07.row880)) (add Basis07.row882 Basis07.row883))) (add (add (add Basis07.row884 node01038) (add (t Basis07.row887) Basis07.row889)) (add (add (t Basis07.row889) Basis07.row890) (add Basis07.row892 node01970)))))))))

private theorem row174 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 174 (0, 0)) ((rowsAt 10).getD 174 (0, 0)) := by
  apply of_certificate witness174
  · decide +kernel
  · decide +kernel

private noncomputable def witness175 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row048

private theorem row175 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 175 (0, 0)) ((rowsAt 10).getD 175 (0, 0)) := by
  apply of_certificate witness175
  · decide +kernel
  · decide +kernel

private noncomputable def witness176 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add node00582 (add Basis07.row002 Basis07.row003)) (add (add node03050 node01064) (add Basis07.row013 node03361))) (add (add (t Basis07.row017) (add Basis07.row020 (t Basis07.row021))) (add (add (t Basis07.row022) (t Basis07.row024)) (add Basis07.row025 node03618)))) (add (add (add Basis07.row030 (add Basis07.row033 node01398)) (add (add node03150 node00220) (add node02441 (t Basis07.row044)))) (add (add (add node03249 node00026) (add (t Basis07.row051) node01758)) (add (add (t Basis07.row054) node03510) (add node00267 (t Basis07.row063)))))) (add (add (add (add Basis07.row064 (add node02654 (t Basis07.row067))) (add (add node00269 node02934) (add node01174 node00285))) (add (add (add node01888 (t Basis07.row079)) (add node00055 Basis07.row083)) (add (add Basis07.row084 Basis07.row086) (add node03667 (t Basis07.row092))))) (add (add (add node01149 (add Basis07.row096 (t Basis07.row096))) (add (add Basis07.row098 Basis07.row099) (add node01818 node02406))) (add (add (add node01339 Basis07.row107) (add node02713 Basis07.row109)) (add (add node02674 Basis07.row113) (add Basis07.row114 node01683)))))) (add (add (add (add (add Basis07.row117 (add (t Basis07.row117) node00363)) (add (add Basis07.row120 node02667) (add Basis07.row124 node00593))) (add (add (add (t Basis07.row128) node01023) (add node04123 node00560)) (add (add node00909 node00479) (add node00736 node00107)))) (add (add (add Basis07.row146 (add node02084 node04398)) (add (add node00561 node01646) (add (t Basis07.row156) node04249))) (add (add (add node03054 Basis07.row163) (add Basis07.row164 node00571)) (add (add node01297 Basis07.row174) (add (t Basis07.row174) node03961))))) (add (add (add (add node00239 (add node02425 (t Basis07.row184))) (add (add node00498 node01238) (add node00057 node03253))) (add (add (add node02136 node01765) (add (t Basis07.row198) node03660)) (add (add node00093 node00192) (add (t Basis07.row206) node00393)))) (add (add (add node00394 (add node01952 node00595)) (add (add node01223 (t Basis07.row219)) (add node04267 node00094))) (add (add (add Basis07.row226 (t Basis07.row226)) (add node01554 node02783)) (add (add Basis07.row232 node03517) (add node02228 node02642))))))) (add (add (add (add (add (add node01583 (add node01089 Basis07.row243)) (add (add (t Basis07.row245) node00783) (add (t Basis07.row247) (t Basis07.row251)))) (add (add node02748 (add node01045 node03000)) (add (add Basis07.row263 Basis07.row264) (add (t Basis07.row264) (t Basis07.row265))))) (add (add (add Basis07.row268 (add node01436 (t Basis07.row271))) (add (add node01413 node00272) (add node02656 node01558))) (add (add (add Basis07.row283 node00596) (add node01446 (t Basis07.row290))) (add (add node01537 (t Basis07.row293)) (add (t Basis07.row294) (t Basis07.row296)))))) (add (add (add (add Basis07.row298 (add Basis07.row299 (t Basis07.row302))) (add (add node04349 Basis07.row310) (add node00150 node00868))) (add (add (add Basis07.row318 node02773) (add node00420 node00013)) (add (add node01401 node02968) (add Basis07.row335 (t Basis07.row336))))) (add (add (add Basis07.row337 (add node01653 (t Basis07.row340))) (add (add Basis07.row341 Basis07.row342) (add Basis07.row343 (t Basis07.row344)))) (add (add (add node00784 (t Basis07.row349)) (add node02596 node00987)) (add (add Basis07.row355 node01416) (add node00725 Basis07.row365)))))) (add (add (add (add (add node03983 (add node00482 Basis07.row374)) (add (add node00444 (t Basis07.row378)) (add node03201 node00336))) (add (add (add node04058 node00981) (add node01562 (t Basis07.row390))) (add (add node01277 Basis07.row393) (add Basis07.row397 node03818)))) (add (add (add node02449 (add node01443 node00574)) (add (add Basis07.row410 (t Basis07.row412)) (add (t Basis07.row413) Basis07.row416))) (add (add (add node01973 Basis07.row419) (add (t Basis07.row419) (t Basis07.row421))) (add (add (t Basis07.row425) Basis07.row426) (add node02377 Basis07.row429))))) (add (add (add (add node02842 (add node03377 Basis07.row437)) (add (add (t Basis07.row437) (t Basis07.row438)) (add Basis07.row440 (t Basis07.row441)))) (add (add (add node04137 Basis07.row446) (add Basis07.row447 node00852)) (add (add node03036 node00931) (add node02056 node02001)))) (add (add (add node03640 (add Basis07.row460 Basis07.row462)) (add (add node00524 (t Basis07.row466)) (add node00706 node01541))) (add (add (add Basis07.row471 (t Basis07.row471)) (add Basis07.row473 Basis07.row474)) (add (add Basis07.row475 node02634) (add node02926 Basis07.row484)))))))) (add (add (add (add (add (add (add Basis07.row485 (add Basis07.row486 Basis07.row487)) (add (add (t Basis07.row487) Basis07.row492) (add Basis07.row493 node02004))) (add (add Basis07.row497 (add (t Basis07.row498) node01661)) (add (add node00382 node00429) (add node00739 (t Basis07.row509))))) (add (add (add Basis07.row510 (add node01485 node00174)) (add (add (t Basis07.row515) node01164) (add node00505 node00085))) (add (add (add node01752 (t Basis07.row523)) (add node00488 Basis07.row525)) (add (add node00100 node00261) (add node04310 node02156))))) (add (add (add (add Basis07.row534 (add node02311 (t Basis07.row537))) (add (add node03063 Basis07.row542) (add (t Basis07.row542) node02601))) (add (add (add node03923 Basis07.row548) (add Basis07.row549 node03117)) (add (add Basis07.row553 node01289) (add node00111 Basis07.row559)))) (add (add (add node00934 (add node03771 node00139)) (add (add node00732 node01381) (add Basis07.row568 Basis07.row570))) (add (add (add (t Basis07.row570) node01487) (add (t Basis07.row574) Basis07.row576)) (add (add node01457 (t Basis07.row579)) (add node01608 node00321)))))) (add (add (add (add (add (t Basis07.row586) (add node01971 node02236)) (add (add node02070 node03042) (add Basis07.row598 (t Basis07.row598)))) (add (add (add (t Basis07.row599) (t Basis07.row600)) (add node00322 Basis07.row604)) (add (add (t Basis07.row604) (t Basis07.row607)) (add Basis07.row608 node00815)))) (add (add (add node00033 (add node00140 node02562)) (add (add node00602 node02454) (add node02628 (t Basis07.row622)))) (add (add (add node00007 node03555) (add node02335 node00733)) (add (add node00567 node01117) (add Basis07.row636 (t Basis07.row636)))))) (add (add (add (add (t Basis07.row637) (add node01527 Basis07.row640)) (add (add node01697 Basis07.row643) (add Basis07.row645 Basis07.row646))) (add (add (add node01032 node02132) (add node00923 node02038)) (add (add node00545 Basis07.row657) (add node01275 (t Basis07.row660))))) (add (add (add node03265 (add node01156 node00245)) (add (add (t Basis07.row667) (t Basis07.row668)) (add Basis07.row669 (t Basis07.row670)))) (add (add (add (t Basis07.row672) Basis07.row673) (add (t Basis07.row675) Basis07.row676)) (add (add (t Basis07.row678) Basis07.row679) (add Basis07.row680 (t Basis07.row680)))))))) (add (add (add (add (add (add node01847 (add (t Basis07.row683) Basis07.row685)) (add (add Basis07.row687 node03822) (add Basis07.row692 (t Basis07.row692)))) (add (add node02950 (add node01634 (t Basis07.row698))) (add (add Basis07.row699 Basis07.row700) (add Basis07.row701 (t Basis07.row701))))) (add (add (add node01570 (add node01848 (t Basis07.row706))) (add (add node00929 Basis07.row709) (add node00041 node01779))) (add (add (add node02011 node01462) (add Basis07.row717 node00386)) (add (add node00492 node01254) (add (t Basis07.row726) Basis07.row727))))) (add (add (add (add node01904 (add node04029 node01684)) (add (add node03997 Basis07.row739) (add node01780 (t Basis07.row742)))) (add (add (add node01182 Basis07.row746) (add node01305 Basis07.row752)) (add (add node02160 node00327) (add node01782 (t Basis07.row760))))) (add (add (add Basis07.row761 (add node02087 Basis07.row768)) (add (add Basis07.row769 node03852) (add (t Basis07.row773) (t Basis07.row774)))) (add (add (add Basis07.row775 node00984) (add node00711 node00493)) (add (add (t Basis07.row783) (t Basis07.row784)) (add (t Basis07.row785) Basis07.row787)))))) (add (add (add (add (add node01670 (add Basis07.row791 node02340)) (add (add node02138 node01589) (add node00743 node02777))) (add (add (add node02550 Basis07.row804) (add node03071 node00234)) (add (add node00778 node02523) (add (t Basis07.row813) Basis07.row814)))) (add (add (add (t Basis07.row815) (add (t Basis07.row816) (t Basis07.row817))) (add (add node00659 Basis07.row821) (add Basis07.row822 (t Basis07.row822)))) (add (add (add node00548 (t Basis07.row826)) (add Basis07.row828 (t Basis07.row828))) (add (add (t Basis07.row829) Basis07.row831) (add node01233 node02925))))) (add (add (add (add (t Basis07.row836) (add Basis07.row838 node01211)) (add (add node00692 node00495) (add node04430 node01630))) (add (add (add node02704 node02778) (add Basis07.row857 (t Basis07.row857))) (add (add Basis07.row858 Basis07.row859) (add node01786 Basis07.row862)))) (add (add (add node03127 (add node01378 node00176)) (add (add node00569 node01532) (add node02949 node01198))) (add (add (add node00105 node00625) (add node00455 node02089)) (add (add node01193 Basis07.row890) (add node00169 node00669)))))))))

private theorem row176 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 176 (0, 0)) ((rowsAt 10).getD 176 (0, 0)) := by
  apply of_certificate witness176
  · decide +kernel
  · decide +kernel

private noncomputable def witness177 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add node01884 (add node00132 (t Basis07.row005))) (add (add (t Basis07.row006) Basis07.row008) (add node01234 (t Basis07.row010)))) (add (add (add node00435 (t Basis07.row012)) (add node02680 node00054)) (add (add node02514 node00114) (add Basis07.row021 node01474)))) (add (add (add (add node00634 Basis07.row025) (add node00282 node00219)) (add (add Basis07.row031 node00635) (add node00090 node02953))) (add (add (add (t Basis07.row038) node03362) (add (t Basis07.row041) Basis07.row045)) (add (add (t Basis07.row045) Basis07.row046) (add node01675 node02079))))) (add (add (add (add (add node01302 Basis07.row058) (add node03291 (t Basis07.row062))) (add (add (t Basis07.row064) node02654) (add (t Basis07.row067) (t Basis07.row069)))) (add (add (add (t Basis07.row070) node00608) (add node04393 (t Basis07.row076))) (add (add node01888 (t Basis07.row079)) (add (t Basis07.row081) (t Basis07.row082))))) (add (add (add (add (t Basis07.row083) Basis07.row084) (add (t Basis07.row085) (t Basis07.row086))) (add (add Basis07.row087 Basis07.row088) (add (t Basis07.row088) (t Basis07.row089)))) (add (add (add node01405 Basis07.row093) (add node01307 node00378)) (add (add node00361 node03636) (add Basis07.row104 node01338)))))) (add (add (add (add (add Basis07.row107 (add node02215 (t Basis07.row111))) (add (add node03733 (t Basis07.row115)) (add Basis07.row116 (t Basis07.row120)))) (add (add (add Basis07.row121 node02973) (add (t Basis07.row124) Basis07.row125)) (add (add Basis07.row126 node03907) (add node04463 node00560)))) (add (add (add (add (t Basis07.row137) node02632) (add (t Basis07.row140) Basis07.row143)) (add (add (t Basis07.row143) node00515) (add node02433 node01024))) (add (add (add Basis07.row151 (t Basis07.row151)) (add node00561 Basis07.row154)) (add (add (t Basis07.row155) (t Basis07.row156)) (add Basis07.row157 node00439))))) (add (add (add (add (add node00018 node03516) (add Basis07.row164 (t Basis07.row167))) (add (add Basis07.row168 Basis07.row169) (add node01553 node02307))) (add (add (add (t Basis07.row175) Basis07.row176) (add node00056 (t Basis07.row181))) (add (add (t Basis07.row182) (t Basis07.row183)) (add node02137 node00270)))) (add (add (add (add Basis07.row189 node04400) (add node00271 node00240)) (add (add (t Basis07.row195) Basis07.row196) (add node02082 Basis07.row199))) (add (add (add (t Basis07.row202) (t Basis07.row203)) (add Basis07.row205 (t Basis07.row205))) (add (add (t Basis07.row207) (t Basis07.row208)) (add (t Basis07.row210) node01349))))))) (add (add (add (add (add (add (t Basis07.row215) (add node03102 node01453)) (add (add Basis07.row222 (t Basis07.row223)) (add Basis07.row225 (t Basis07.row226)))) (add (add (add node01601 Basis07.row230) (add (t Basis07.row230) (t Basis07.row231))) (add (add node03517 (t Basis07.row235)) (add Basis07.row236 node01449)))) (add (add (add (add node01708 Basis07.row241) (add node00499 (t Basis07.row244))) (add (add Basis07.row248 (t Basis07.row249)) (add node01602 node00481))) (add (add (add node01027 (t Basis07.row257)) (add Basis07.row258 Basis07.row259)) (add (add node00761 (t Basis07.row265)) (add (t Basis07.row267) (t Basis07.row269)))))) (add (add (add (add (add node00058 node02512) (add node00272 node03747)) (add (add node01804 node02037) (add Basis07.row283 node03237))) (add (add (add node01972 node01559) (add node00921 node03373)) (add (add node00953 node01560) (add node03638 Basis07.row305)))) (add (add (add (add (t Basis07.row306) Basis07.row309) (add (t Basis07.row309) Basis07.row312)) (add (add Basis07.row313 (t Basis07.row314)) (add node01225 (t Basis07.row317)))) (add (add (add node00136 (t Basis07.row321)) (add (t Basis07.row323) Basis07.row325)) (add (add Basis07.row326 node00803) (add node03257 node01125)))))) (add (add (add (add (add node00163 (add node03469 (t Basis07.row338))) (add (add node02956 node01520) (add Basis07.row347 (t Basis07.row347)))) (add (add (add node02100 node00109) (add Basis07.row353 Basis07.row354)) (add (add node02752 (t Basis07.row356)) (add node01878 Basis07.row360)))) (add (add (add (add node00612 Basis07.row363) (add Basis07.row366 (t Basis07.row366))) (add (add Basis07.row368 Basis07.row369) (add node00422 node04464))) (add (add (add (t Basis07.row376) node00256) (add Basis07.row379 Basis07.row380)) (add (add (t Basis07.row380) Basis07.row382) (add Basis07.row383 Basis07.row384))))) (add (add (add (add (add node00809 (t Basis07.row387)) (add (t Basis07.row388) node03719)) (add (add node01098 node02263) (add node00462 node03843))) (add (add (add node01713 (t Basis07.row406)) (add (t Basis07.row407) node00137)) (add (add Basis07.row411 node00564) (add node00463 node01292)))) (add (add (add (add (t Basis07.row420) node02834) (add (t Basis07.row425) Basis07.row426)) (add (add Basis07.row427 Basis07.row428) (add Basis07.row429 Basis07.row430))) (add (add (add node00484 node03378) (add node03659 node02719)) (add (add node01507 node03986) (add node00653 (t Basis07.row448))))))))) (add (add (add (add (add (add (add node03820 (add Basis07.row452 (t Basis07.row452))) (add (add node02349 node00260) (add node02997 node01390))) (add (add (add node00523 Basis07.row465) (add (t Basis07.row466) Basis07.row467)) (add (add Basis07.row468 Basis07.row469) (add (t Basis07.row469) node03061)))) (add (add (add (add node02873 node03630) (add node00600 node01925)) (add (add Basis07.row481 node01185) (add node01107 node02494))) (add (add (add (t Basis07.row488) Basis07.row489) (add node02495 (t Basis07.row492))) (add (add node01293 node01839) (add node04480 (t Basis07.row501)))))) (add (add (add (add (add (t Basis07.row502) (t Basis07.row503)) (add node00382 node01662)) (add (add node01310 Basis07.row510) (add (t Basis07.row511) (t Basis07.row512)))) (add (add (add Basis07.row513 node01469) (add Basis07.row516 node00505)) (add (add Basis07.row519 node01356) (add Basis07.row523 node03062)))) (add (add (add (add node00849 node01802) (add node02577 (t Basis07.row532))) (add (add node00954 (t Basis07.row535)) (add node01312 (t Basis07.row540)))) (add (add (add node00526 Basis07.row545) (add (t Basis07.row545) (t Basis07.row546))) (add (add node00195 Basis07.row549) (add (t Basis07.row550) (t Basis07.row551))))))) (add (add (add (add (add Basis07.row552 (add (t Basis07.row554) Basis07.row555)) (add (add node01077 node02112) (add (t Basis07.row560) node00466))) (add (add (add node02730 node01258) (add node00912 (t Basis07.row569))) (add (add Basis07.row571 (t Basis07.row571)) (add node01358 (t Basis07.row576))))) (add (add (add (add Basis07.row577 Basis07.row578) (add Basis07.row579 Basis07.row581)) (add (add Basis07.row583 node00682) (add node00955 node01429))) (add (add (add (t Basis07.row589) node03005) (add node00872 node03601)) (add (add (t Basis07.row598) (t Basis07.row599)) (add node00935 Basis07.row603))))) (add (add (add (add (add (t Basis07.row603) Basis07.row606) (add (t Basis07.row607) Basis07.row608)) (add (add (t Basis07.row608) (t Basis07.row610)) (add node00965 node00873))) (add (add (add node01245 Basis07.row620) (add (t Basis07.row621) Basis07.row622)) (add (add Basis07.row623 (t Basis07.row626)) (add node00126 node04453)))) (add (add (add (add Basis07.row633 node04032) (add (t Basis07.row637) node03390)) (add (add node03067 Basis07.row644) (add (t Basis07.row644) (t Basis07.row645)))) (add (add (add (t Basis07.row646) node01460) (add Basis07.row651 Basis07.row652)) (add (add node01778 Basis07.row655) (add node00407 node01916))))))) (add (add (add (add (add (add Basis07.row662 (add node03266 Basis07.row666)) (add (add (t Basis07.row667) node01123) (add node02353 node00656))) (add (add (add node00886 node03715) (add (t Basis07.row682) Basis07.row685)) (add (add node01287 Basis07.row688) (add Basis07.row689 (t Basis07.row689))))) (add (add (add (add node01666 node03542) (add Basis07.row696 Basis07.row697)) (add (add node01085 node00657) (add node02118 (t Basis07.row704)))) (add (add (add node00723 (t Basis07.row707)) (add (t Basis07.row709) Basis07.row710)) (add (add node02647 node01902) (add node02174 node04092))))) (add (add (add (add (add node01034 node02382) (add node01611 node03165)) (add (add (t Basis07.row728) (t Basis07.row731)) (add Basis07.row732 node01849))) (add (add (add Basis07.row735 node00915) (add (t Basis07.row739) (t Basis07.row741))) (add (add (t Basis07.row742) Basis07.row744) (add node02362 node00295)))) (add (add (add (add node00263 Basis07.row751) (add Basis07.row752 node01473)) (add (add (t Basis07.row758) (t Basis07.row759)) (add Basis07.row760 node00062))) (add (add (add node01492 node02161) (add node01529 (t Basis07.row771))) (add (add Basis07.row772 (t Basis07.row772)) (add (t Basis07.row773) (t Basis07.row774))))))) (add (add (add (add (add node00102 (add node00711 node00103)) (add (add Basis07.row785 Basis07.row786) (add node00030 Basis07.row789))) (add (add (add (t Basis07.row791) node01678) (add Basis07.row796 node02249)) (add (add (t Basis07.row799) node00280) (add (t Basis07.row803) node02268)))) (add (add (add (add node00281 node00454) (add node01352 (t Basis07.row813))) (add (add (t Basis07.row814) (t Basis07.row815)) (add Basis07.row817 node03936))) (add (add (add node02252 (t Basis07.row823)) (add Basis07.row825 (t Basis07.row828))) (add (add node00144 node03953) (add node00880 node04273))))) (add (add (add (add (add Basis07.row838 node04195) (add node02422 Basis07.row843)) (add (add Basis07.row845 Basis07.row846) (add (t Basis07.row847) node00645))) (add (add (add node04431 node00752) (add node00675 (t Basis07.row858))) (add (add Basis07.row859 Basis07.row860) (add Basis07.row861 Basis07.row862)))) (add (add (add (add node03323 node00145) (add Basis07.row868 node01426)) (add (add (t Basis07.row873) node01290) (add node01187 (t Basis07.row878)))) (add (add (add node00105 node00877) (add node00455 node00605)) (add (add (t Basis07.row888) node02501) (add node01303 node00669)))))))))

private theorem row177 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 177 (0, 0)) ((rowsAt 10).getD 177 (0, 0)) := by
  apply of_certificate witness177
  · decide +kernel
  · decide +kernel

private noncomputable def witness178 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row049

private theorem row178 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 178 (0, 0)) ((rowsAt 10).getD 178 (0, 0)) := by
  apply of_certificate witness178
  · decide +kernel
  · decide +kernel

private noncomputable def witness179 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add (t Basis07.row001) (add Basis07.row003 node01939)) (add (add node02366 node01097) (add node03082 (t Basis07.row012)))) (add (add (add node03945 node02514) (add node00842 node02887)) (add (add node00918 Basis07.row027) (add Basis07.row028 Basis07.row029)))) (add (add (add Basis07.row030 (add node01432 (t Basis07.row033))) (add (add Basis07.row035 Basis07.row037) (add Basis07.row038 Basis07.row041))) (add (add (add node01450 node01475) (add Basis07.row047 node01675)) (add (add (t Basis07.row050) (t Basis07.row051)) (add (t Basis07.row052) (t Basis07.row053)))))) (add (add (add (add (t Basis07.row055) (add Basis07.row058 node02902)) (add (add node01294 node02849) (add (t Basis07.row068) (t Basis07.row070)))) (add (add (add Basis07.row072 node03352) (add Basis07.row075 node00609)) (add (add Basis07.row079 node00134) (add Basis07.row081 (t Basis07.row083))))) (add (add (add (add (t Basis07.row084) node02850) (add node01021 node00570)) (add (add node03081 Basis07.row096) (add node00361 node00636))) (add (add (add Basis07.row104 (t Basis07.row104)) (add node02094 node03977)) (add (add Basis07.row114 (t Basis07.row115)) (add Basis07.row117 node03512)))))) (add (add (add (add (add Basis07.row120 (add node00437 node02623)) (add (add node01550 node04106) (add Basis07.row135 Basis07.row136))) (add (add (add node02632 (t Basis07.row141)) (add (t Basis07.row142) (t Basis07.row143))) (add (add node01639 Basis07.row147) (add (t Basis07.row147) (t Basis07.row148))))) (add (add (add node02607 (add node00161 node00250)) (add (add node01949 node00786) (add node00018 node00537))) (add (add (add node02327 Basis07.row165) (add Basis07.row166 node00571)) (add (add node00754 node00288) (add node02624 (t Basis07.row175)))))) (add (add (add (add Basis07.row176 (add Basis07.row178 node01823)) (add (add node00239 node02281) (add node00594 node00498))) (add (add (add node00766 node00416) (add (t Basis07.row192) node02589)) (add (add Basis07.row195 node01950) (add Basis07.row200 (t Basis07.row201))))) (add (add (add (add node04386 node01291) (add node02716 node00108)) (add (add node01382 (t Basis07.row218)) (add Basis07.row221 node00704))) (add (add (add (t Basis07.row223) node02898) (add node01274 Basis07.row231)) (add (add (t Basis07.row231) (t Basis07.row232)) (add Basis07.row233 Basis07.row236))))))) (add (add (add (add (add (add Basis07.row238 (add Basis07.row239 node01089)) (add (add node01502 Basis07.row246) (add Basis07.row248 node04054))) (add (add (add node00750 node02485) (add Basis07.row257 node00812)) (add (add node00970 node00366) (add Basis07.row264 Basis07.row265)))) (add (add (add node03254 (add Basis07.row269 (t Basis07.row271))) (add (add node00772 node01028) (add (t Basis07.row278) (t Basis07.row279)))) (add (add (add node02374 node00301) (add node02033 Basis07.row287)) (add (add node01895 node00149) (add Basis07.row293 (t Basis07.row295)))))) (add (add (add (add Basis07.row297 (add (t Basis07.row297) (t Basis07.row298))) (add (add Basis07.row300 node02574) (add node03486 (t Basis07.row305)))) (add (add (add Basis07.row306 node01768) (add node00047 node00737)) (add (add node00443 node00867) (add node00243 node01225)))) (add (add (add (add node01047 node03706) (add (t Basis07.row321) node00882)) (add (add (t Basis07.row325) node02519) (add node02149 Basis07.row336))) (add (add (add node00995 (t Basis07.row338)) (add node01285 node00542)) (add (add node01316 node01955) (add node00121 (t Basis07.row347))))))) (add (add (add (add (add Basis07.row350 (add node00109 node04494)) (add (add (t Basis07.row355) (t Basis07.row356)) (add Basis07.row357 (t Basis07.row358)))) (add (add (add (t Basis07.row359) node03764) (add (t Basis07.row362) Basis07.row365)) (add (add Basis07.row366 (t Basis07.row366)) (add node01998 node02262)))) (add (add (add Basis07.row372 (add Basis07.row373 node00048)) (add (add (t Basis07.row375) (t Basis07.row376)) (add Basis07.row378 (t Basis07.row378)))) (add (add (add node03523 (t Basis07.row381)) (add (t Basis07.row382) node03807)) (add (add Basis07.row386 (t Basis07.row388)) (add node01049 Basis07.row392))))) (add (add (add (add Basis07.row394 (add (t Basis07.row394) node00424)) (add (add node00462 (t Basis07.row399)) (add (t Basis07.row400) node03892))) (add (add (add node02331 Basis07.row406) (add node01882 node01280)) (add (add node01770 node02725) (add (t Basis07.row415) (t Basis07.row416))))) (add (add (add (add (t Basis07.row417) Basis07.row420) (add (t Basis07.row420) node00521)) (add (add node03111 Basis07.row427) (add Basis07.row428 (t Basis07.row429)))) (add (add (add Basis07.row430 Basis07.row432) (add node01897 (t Basis07.row438))) (add (add Basis07.row440 node00427) (add Basis07.row443 (t Basis07.row444))))))))) (add (add (add (add (add (add (add Basis07.row445 (add node02911 (t Basis07.row448))) (add (add (t Basis07.row449) (t Basis07.row451)) (add (t Basis07.row452) node00209))) (add (add (add node02492 node01564) (add node00153 (t Basis07.row462))) (add (add node03046 (t Basis07.row466)) (add Basis07.row467 Basis07.row468)))) (add (add (add (t Basis07.row469) (add node01195 node02912)) (add (add node00575 node02634) (add (t Basis07.row478) node00738))) (add (add (add node00791 node02738) (add node01863 (t Basis07.row487))) (add (add node03262 Basis07.row493) (add (t Basis07.row493) Basis07.row497))))) (add (add (add (add Basis07.row498 (add node01076 node02294)) (add (add (t Basis07.row502) (t Basis07.row504)) (add node00739 node01420))) (add (add (add Basis07.row510 node03129) (add node01469 node03187)) (add (add node03385 node01268) (add node01155 Basis07.row524)))) (add (add (add (add Basis07.row525 node00849) (add node01720 node02577)) (add (add (t Basis07.row532) node00078) (add node02877 node04067))) (add (add (add (t Basis07.row540) Basis07.row541) (add Basis07.row542 node02135)) (add (add Basis07.row545 (t Basis07.row545)) (add node02057 (t Basis07.row549))))))) (add (add (add (add (add Basis07.row550 (add node00911 node01841)) (add (add node00566 node04101) (add (t Basis07.row558) node00934))) (add (add (add Basis07.row561 node03075) (add Basis07.row565 Basis07.row566)) (add (add node02866 node01016) (add Basis07.row572 node01487)))) (add (add (add node03211 (add node02039 node00846)) (add (add (t Basis07.row582) node01642) (add node00955 (t Basis07.row587)))) (add (add (add (t Basis07.row590) node00229) (add node02114 node00489)) (add (add node02031 (t Basis07.row605)) (add Basis07.row607 (t Basis07.row609)))))) (add (add (add (add node02258 (add node02321 node01899)) (add (add (t Basis07.row617) (t Basis07.row618)) (add Basis07.row619 Basis07.row621))) (add (add (add (t Basis07.row622) node02629) (add (t Basis07.row626) Basis07.row627)) (add (add node01664 node01610) (add node00384 Basis07.row635)))) (add (add (add (add (t Basis07.row636) (t Basis07.row638)) (add (t Basis07.row639) node01697)) (add (add (t Basis07.row643) (t Basis07.row644)) (add node04318 node01460))) (add (add (add (t Basis07.row652) node01096) (add node00112 node02617)) (add (add (t Basis07.row660) Basis07.row662) (add node00821 node03267))))))) (add (add (add (add (add (add node00200 (add node00836 node00373)) (add (add node01920 node00917) (add node00811 node00385))) (add (add (add Basis07.row684 (t Basis07.row684)) (add node02552 node02944)) (add (add node00008 (t Basis07.row691)) (add node03662 Basis07.row696)))) (add (add (add Basis07.row699 (add node03397 node02390)) (add (add node02198 Basis07.row708) (add node04424 Basis07.row711))) (add (add (add Basis07.row712 Basis07.row713) (add Basis07.row714 node00006)) (add (add node00578 Basis07.row718) (add Basis07.row719 node02260))))) (add (add (add (add (t Basis07.row723) (add node01141 node02921)) (add (add node01612 (t Basis07.row732)) (add (t Basis07.row733) Basis07.row735))) (add (add (add Basis07.row736 node00216) (add node04344 (t Basis07.row743))) (add (add node00756 (t Basis07.row746)) (add Basis07.row749 Basis07.row750)))) (add (add (add (add (t Basis07.row750) node03781) (add node00767 node03217)) (add (add node00062 Basis07.row763) (add Basis07.row766 Basis07.row768))) (add (add (add node01727 node03743) (add node03146 Basis07.row777)) (add (add node00409 node03231) (add (t Basis07.row785) node01279)))))) (add (add (add (add (add node00063 (add node02386 (t Basis07.row792))) (add (add (t Basis07.row793) node01203) (add Basis07.row797 Basis07.row798))) (add (add (add Basis07.row800 node01989) (add node00633 Basis07.row806)) (add (add Basis07.row808 node02756) (add Basis07.row812 Basis07.row813)))) (add (add (add (t Basis07.row817) (add node01109 node00919)) (add (add node02344 Basis07.row825) (add node00604 node00690))) (add (add (add node00144 node01785) (add node03856 node00862)) (add (add node04237 (t Basis07.row841)) (add (t Basis07.row842) (t Basis07.row843)))))) (add (add (add (add (t Basis07.row844) (add (t Basis07.row845) node01672)) (add (add (t Basis07.row849) Basis07.row850) (add node00623 Basis07.row854))) (add (add (add Basis07.row856 Basis07.row857) (add Basis07.row859 node01786)) (add (add node02882 Basis07.row865) (add Basis07.row866 node01003)))) (add (add (add (add (t Basis07.row869) node02389) (add node00177 Basis07.row876)) (add (add node03578 Basis07.row881) (add (t Basis07.row882) Basis07.row884))) (add (add (add Basis07.row885 (t Basis07.row886)) (add Basis07.row887 node00660)) (add (add (t Basis07.row890) Basis07.row891) (add node02603 (t Basis07.row894))))))))))

private theorem row179 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 179 (0, 0)) ((rowsAt 10).getD 179 (0, 0)) := by
  apply of_certificate witness179
  · decide +kernel
  · decide +kernel

private noncomputable def witness180 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row427

private theorem row180 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 180 (0, 0)) ((rowsAt 10).getD 180 (0, 0)) := by
  apply of_certificate witness180
  · decide +kernel
  · decide +kernel

private noncomputable def witness181 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add Basis07.row001 (add (t Basis07.row002) node02805)) (add (add node04293 node00414) (add (t Basis07.row009) node00435))) (add (add (add (t Basis07.row012) (t Basis07.row013)) (add node04046 Basis07.row020)) (add (add (t Basis07.row023) node03727) (add Basis07.row027 Basis07.row028)))) (add (add (add (add (t Basis07.row028) (t Basis07.row029)) (add (t Basis07.row030) (t Basis07.row032))) (add (add Basis07.row033 node02475) (add node03814 (t Basis07.row039)))) (add (add (add node02040 node01699) (add Basis07.row046 node01549)) (add (add Basis07.row049 Basis07.row050) (add Basis07.row052 node01594))))) (add (add (add (add node02848 (add node01700 node01103)) (add (add node01294 (t Basis07.row064)) (add node01375 Basis07.row068))) (add (add (add node00916 Basis07.row072) (add node00962 (t Basis07.row075))) (add (add node00609 node00191) (add node01104 node02274)))) (add (add (add (add node01736 node02092) (add node02813 node01086)) (add (add node02556 (t Basis07.row093)) (add node01361 (t Basis07.row099)))) (add (add (add Basis07.row101 Basis07.row102) (add (t Basis07.row103) Basis07.row106)) (add (add Basis07.row107 (t Basis07.row107)) (add (t Basis07.row108) (t Basis07.row111))))))) (add (add (add (add (add node03733 (add node01683 Basis07.row117)) (add (add (t Basis07.row118) (t Basis07.row120)) (add node01242 node00170))) (add (add (add (t Basis07.row124) Basis07.row125) (add Basis07.row126 node02606)) (add (add node00075 node00457) (add node04333 node01551)))) (add (add (add (add node01948 (t Basis07.row141)) (add node00515 Basis07.row148)) (add (add node01065 node01761) (add node01308 (t Basis07.row154)))) (add (add (add Basis07.row156 node03584) (add Basis07.row161 node03154)) (add (add Basis07.row164 (t Basis07.row165)) (add node01640 Basis07.row169))))) (add (add (add (add (add (t Basis07.row169) (t Basis07.row170)) (add Basis07.row173 (t Basis07.row173))) (add (add Basis07.row176 node01540) (add node02046 Basis07.row181))) (add (add (add (t Basis07.row182) (t Basis07.row183)) (add Basis07.row184 node02429)) (add (add (t Basis07.row187) Basis07.row188) (add node01516 Basis07.row191)))) (add (add (add (add node02354 Basis07.row196) (add node01950 node00893)) (add (add node02903 node01004) (add Basis07.row206 node02557))) (add (add (add node01410 (t Basis07.row210)) (add node01349 (t Basis07.row213))) (add (add node02717 Basis07.row217) (add node01453 node01600))))))) (add (add (add (add (add (add (t Basis07.row222) (add node03644 Basis07.row229)) (add (add node02783 Basis07.row232) (add node04271 Basis07.row235))) (add (add (add Basis07.row236 Basis07.row237) (add Basis07.row238 node01583)) (add (add node03044 Basis07.row243) (add node01995 Basis07.row246)))) (add (add (add (add node02609 Basis07.row250) (add (t Basis07.row251) node00014)) (add (add Basis07.row255 (t Basis07.row256)) (add node02559 Basis07.row260))) (add (add (add node02186 Basis07.row263) (add (t Basis07.row263) (t Basis07.row265))) (add (add node03587 Basis07.row269) (add (t Basis07.row269) (t Basis07.row270)))))) (add (add (add (add node02320 (add node01121 node03299)) (add (add node00539 Basis07.row281) (add node01011 node03186))) (add (add (add node02510 (t Basis07.row289)) (add (t Basis07.row290) node01826)) (add (add node00628 node00207) (add Basis07.row300 Basis07.row301)))) (add (add (add (add Basis07.row302 node03519) (add Basis07.row305 Basis07.row307)) (add (add (t Basis07.row307) (t Basis07.row308)) (add node02177 node01091))) (add (add (add node03679 (t Basis07.row317)) (add node00136 (t Basis07.row322))) (add (add (t Basis07.row323) node00420) (add node03795 node04098)))))) (add (add (add (add (add (t Basis07.row332) (add Basis07.row334 Basis07.row336)) (add (add node00995 (t Basis07.row340)) (add (t Basis07.row341) node01427))) (add (add (add Basis07.row344 node03891) (add (t Basis07.row348) node01218)) (add (add node01215 node01416) (add node03185 node03499)))) (add (add (add (add node00845 node00083) (add Basis07.row370 node02896)) (add (add node01199 node01709) (add node01083 node03523))) (add (add (add (t Basis07.row381) node03286) (add (t Basis07.row386) (t Basis07.row388))) (add (add node03719 Basis07.row392) (add node01098 Basis07.row396))))) (add (add (add (add (add (t Basis07.row396) Basis07.row399) (add node02808 node01224)) (add (add node00630 node03802) (add (t Basis07.row409) (t Basis07.row410)))) (add (add (add node02699 node01931) (add node02025 node03505)) (add (add node01833 node00173) (add node00982 Basis07.row427)))) (add (add (add (add Basis07.row428 node02000) (add node00338 node04061)) (add (add Basis07.row436 node03260) (add Basis07.row439 node02504))) (add (add (add Basis07.row443 Basis07.row444) (add Basis07.row445 node02767)) (add (add (t Basis07.row449) node03563) (add (t Basis07.row453) Basis07.row457)))))))) (add (add (add (add (add (add (add node01564 (add (t Basis07.row461) node00464)) (add (add Basis07.row465 node01014) (add Basis07.row468 node01659))) (add (add (add (t Basis07.row472) (t Basis07.row473)) (add (t Basis07.row474) Basis07.row475)) (add (add (t Basis07.row475) (t Basis07.row477)) (add node00738 Basis07.row482)))) (add (add (add (add (t Basis07.row482) Basis07.row484) (add Basis07.row485 Basis07.row486)) (add (add (t Basis07.row486) node01137) (add (t Basis07.row490) Basis07.row492))) (add (add (add node01717 node00318) (add Basis07.row497 (t Basis07.row498))) (add (add node00447 (t Basis07.row502)) (add Basis07.row504 Basis07.row507))))) (add (add (add (add node00504 (add (t Basis07.row510) node02234)) (add (add node01917 Basis07.row515) (add Basis07.row516 (t Basis07.row517)))) (add (add (add Basis07.row520 Basis07.row521) (add (t Basis07.row521) node03485)) (add (add node00069 (t Basis07.row526)) (add node01840 node00156)))) (add (add (add (add node01641 (t Basis07.row533)) (add Basis07.row537 node03023)) (add (add node00275 node02110) (add Basis07.row547 node02295))) (add (add (add node01974 Basis07.row553) (add Basis07.row554 Basis07.row555)) (add (add Basis07.row558 Basis07.row559) (add (t Basis07.row559) node01181)))))) (add (add (add (add (add (t Basis07.row565) (add node03076 node01016)) (add (add node00039 node01567) (add node00898 node00070))) (add (add (add Basis07.row579 (t Basis07.row579)) (add node01924 Basis07.row583)) (add (add node00342 node00955) (add node01429 node00973)))) (add (add (add (add node04225 node01898) (add node00905 (t Basis07.row597))) (add (add node01803 node01189) (add (t Basis07.row602) node01278))) (add (add (add (t Basis07.row606) Basis07.row607) (add node03810 Basis07.row611)) (add (add Basis07.row613 (t Basis07.row614)) (add Basis07.row616 Basis07.row618))))) (add (add (add (add (add node03027 (t Basis07.row623)) (add Basis07.row624 (t Basis07.row627))) (add (add Basis07.row630 node01610) (add Basis07.row634 node03457))) (add (add (add node01527 node00305) (add node00854 (t Basis07.row643))) (add (add Basis07.row645 (t Basis07.row646)) (add node01638 node01488)))) (add (add (add (add Basis07.row655 node04242) (add node01916 node02941)) (add (add Basis07.row663 node01056) (add node01250 Basis07.row668))) (add (add (add Basis07.row670 Basis07.row671) (add (t Basis07.row671) node01543)) (add (add node01626 Basis07.row677) (add Basis07.row678 (t Basis07.row678)))))))) (add (add (add (add (add (add (t Basis07.row680) (add Basis07.row682 (t Basis07.row682))) (add (add (t Basis07.row684) Basis07.row685) (add Basis07.row686 Basis07.row687))) (add (add (add node01129 node01373) (add node00292 node03543)) (add (add node02063 node04234) (add node00657 (t Basis07.row702))))) (add (add (add (add (t Basis07.row704) (t Basis07.row705)) (add node03460 node03714)) (add (add (t Basis07.row711) Basis07.row712) (add node01864 Basis07.row716))) (add (add (add Basis07.row717 node00142) (add node02382 Basis07.row723)) (add (add node02755 Basis07.row726) (add Basis07.row728 Basis07.row729))))) (add (add (add (add node01407 (add (t Basis07.row732) (t Basis07.row733))) (add (add (t Basis07.row734) Basis07.row735) (add node00556 node04344))) (add (add (add (t Basis07.row742) node01080) (add node00756 node01265)) (add (add Basis07.row750 Basis07.row751) (add Basis07.row752 node00673)))) (add (add (add (add Basis07.row756 Basis07.row757) (add node02246 Basis07.row760)) (add (add Basis07.row763 Basis07.row764) (add node00579 (t Basis07.row767)))) (add (add (add (t Basis07.row768) Basis07.row770) (add node00389 node03228)) (add (add Basis07.row777 (t Basis07.row777)) (add (t Basis07.row778) node03574)))))) (add (add (add (add (add (t Basis07.row783) (add Basis07.row785 Basis07.row786)) (add (add node02201 Basis07.row789) (add node00683 node01434))) (add (add (add node03824 (t Basis07.row796)) (add (t Basis07.row797) (t Basis07.row799))) (add (add (t Basis07.row801) (t Basis07.row802)) (add Basis07.row803 (t Basis07.row804))))) (add (add (add (add node04495 node03124) (add node01352 Basis07.row813)) (add (add node01808 node00659) (add node01143 Basis07.row822))) (add (add (add Basis07.row823 (t Basis07.row823)) (add node03011 node04484)) (add (add node03993 node03969) (add (t Basis07.row835) Basis07.row837))))) (add (add (add (add (add Basis07.row839 (t Basis07.row840)) (add (t Basis07.row841) (t Basis07.row842))) (add (add (t Basis07.row844) (t Basis07.row845)) (add (t Basis07.row848) Basis07.row850))) (add (add (add (t Basis07.row852) (t Basis07.row853)) (add (t Basis07.row855) Basis07.row856)) (add (add (t Basis07.row856) (t Basis07.row859)) (add node02019 Basis07.row863)))) (add (add (add (add Basis07.row864 node01855) (add node00330 node02884)) (add (add node01787 (t Basis07.row873)) (add Basis07.row876 (t Basis07.row876)))) (add (add (add (t Basis07.row878) node04019) (add node00877 Basis07.row885)) (add (add node01193 node02253) (add node02399 Basis07.row894)))))))))

private theorem row181 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 181 (0, 0)) ((rowsAt 10).getD 181 (0, 0)) := by
  apply of_certificate witness181
  · decide +kernel
  · decide +kernel

private noncomputable def witness182 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add node01148 (add node00132 node03898)) (add (add (t Basis07.row007) (t Basis07.row009)) (add node02900 Basis07.row013))) (add (add (add node00822 node01741) (add node00842 (t Basis07.row023))) (add (add node00918 Basis07.row029) (add node01816 node00635)))) (add (add (add (add node00090 Basis07.row037) (add Basis07.row038 node02476)) (add (add Basis07.row041 Basis07.row042) (add (t Basis07.row042) Basis07.row045))) (add (add (add Basis07.row046 node02619) (add node00357 node00583)) (add (add node02666 node00838) (add node01579 Basis07.row060))))) (add (add (add (add (add (t Basis07.row060) Basis07.row061) (add node01755 (t Basis07.row064))) (add (add node01911 Basis07.row067) (add node00106 Basis07.row071))) (add (add (add node00962 (t Basis07.row075)) (add Basis07.row076 (t Basis07.row076))) (add (add node01944 (t Basis07.row079)) (add Basis07.row080 (t Basis07.row081))))) (add (add (add (add Basis07.row082 Basis07.row083) (add Basis07.row084 node03671)) (add (add node02813 (t Basis07.row089)) (add (t Basis07.row091) (t Basis07.row092)))) (add (add (add node03433 (t Basis07.row096)) (add (t Basis07.row097) Basis07.row100)) (add (add node02822 Basis07.row105) (add Basis07.row106 node02407)))))) (add (add (add (add (add node00627 (add Basis07.row112 (t Basis07.row113))) (add (add (t Basis07.row114) (t Basis07.row115)) (add node01074 node01112))) (add (add (add Basis07.row120 Basis07.row121) (add node00170 node01124)) (add (add node01597 node02586) (add node01005 Basis07.row137)))) (add (add (add (add (t Basis07.row137) (t Basis07.row138)) (add (t Basis07.row139) node00536)) (add (add (t Basis07.row142) node02278) (add node01937 (t Basis07.row149)))) (add (add (add Basis07.row151 (t Basis07.row151)) (add node01704 node00250)) (add (add node03251 Basis07.row159) (add (t Basis07.row160) Basis07.row161))))) (add (add (add (add (add node03368 node01237) (add (t Basis07.row166) Basis07.row170)) (add (add node01553 (t Basis07.row172)) (add node00584 Basis07.row176))) (add (add (add node00755 node00056) (add Basis07.row180 Basis07.row181)) (add (add node00181 node01284) (add Basis07.row188 Basis07.row189)))) (add (add (add (add (t Basis07.row189) node00162) (add node01650 Basis07.row194)) (add (add (t Basis07.row195) Basis07.row197) (add Basis07.row200 Basis07.row201))) (add (add (add node02784 node00252) (add node02716 Basis07.row211)) (add (add node02371 node00969) (add Basis07.row217 (t Basis07.row217)))))))) (add (add (add (add (add (add (t Basis07.row218) (add (t Basis07.row219) node01600)) (add (add Basis07.row224 node04402) (add (t Basis07.row227) node00224))) (add (add (add Basis07.row232 Basis07.row233) (add Basis07.row234 node02145)) (add (add node02869 (t Basis07.row239)) (add Basis07.row240 (t Basis07.row244))))) (add (add (add (add node02807 node00769) (add node03804 Basis07.row252)) (add (add Basis07.row253 Basis07.row254) (add node03980 (t Basis07.row257)))) (add (add (add Basis07.row260 node01518) (add Basis07.row264 Basis07.row265)) (add (add node00398 node00993) (add (t Basis07.row268) (t Basis07.row270)))))) (add (add (add (add (add Basis07.row271 (t Basis07.row272)) (add Basis07.row273 node00952)) (add (add node03747 Basis07.row278) (add node00206 node03300))) (add (add (add node03179 Basis07.row287) (add Basis07.row288 node01895)) (add (add node01467 node00021) (add node01100 node02688)))) (add (add (add (add node01560 (t Basis07.row302)) (add node03138 (t Basis07.row307))) (add (add node01272 Basis07.row311) (add (t Basis07.row311) Basis07.row312))) (add (add (add node00868 node01225) (add Basis07.row320 node03590)) (add (add Basis07.row324 (t Basis07.row326)) (add node00989 (t Basis07.row332))))))) (add (add (add (add (add (add (t Basis07.row334) Basis07.row335) (add node03258 (t Basis07.row338))) (add (add (t Basis07.row339) node02924) (add Basis07.row342 Basis07.row343))) (add (add (add node01309 Basis07.row347) (add node01829 Basis07.row350)) (add (add (t Basis07.row350) node04034) (add node02411 Basis07.row357)))) (add (add (add (add (t Basis07.row358) Basis07.row359) (add Basis07.row362 node04109)) (add (add node03983 (t Basis07.row368)) (add Basis07.row370 Basis07.row371))) (add (add (add node00335 (t Basis07.row374)) (add Basis07.row375 node01342)) (add (add node00256 Basis07.row380) (add (t Basis07.row380) Basis07.row383))))) (add (add (add (add (add node02657 (t Basis07.row386)) (add node01562 node01049)) (add (add node00164 (t Basis07.row393)) (add Basis07.row394 (t Basis07.row394)))) (add (add (add node01958 (t Basis07.row397)) (add (t Basis07.row399) node01252)) (add (add node02055 node01714) (add (t Basis07.row406) (t Basis07.row407))))) (add (add (add (add Basis07.row409 Basis07.row412) (add (t Basis07.row412) node02428)) (add (add node00721 Basis07.row420) (add (t Basis07.row420) node01833))) (add (add (add (t Basis07.row423) Basis07.row424) (add node03526 node01403)) (add (add node03419 node01030) (add (t Basis07.row438) Basis07.row439)))))))) (add (add (add (add (add (add (add (t Basis07.row439) (add node01344 Basis07.row445)) (add (add Basis07.row446 Basis07.row447) (add Basis07.row448 (t Basis07.row448)))) (add (add (add (t Basis07.row449) Basis07.row453) (add Basis07.row454 node01470)) (add (add node01960 node01658) (add node01050 (t Basis07.row465))))) (add (add (add (add (t Basis07.row467) node00614) (add node01440 Basis07.row476)) (add (add Basis07.row478 node01925) (add (t Basis07.row480) node01107))) (add (add (add node03114 node04257) (add node01293 Basis07.row498)) (add (add node02815 node02711) (add node00429 node01276))))) (add (add (add (add (add (t Basis07.row508) node01773) (add (t Basis07.row511) node00174)) (add (add node00303 Basis07.row517) (add Basis07.row519 (t Basis07.row520)))) (add (add (add node03661 node00789) (add node01134 node01720)) (add (add Basis07.row531 node00371) (add node01196 (t Basis07.row535))))) (add (add (add (add (t Basis07.row536) node03721) (add (t Basis07.row542) node02540)) (add (add (t Basis07.row546) (t Basis07.row548)) (add (t Basis07.row549) node03025))) (add (add (add (t Basis07.row554) node03692) (add node01271 (t Basis07.row560))) (add (add Basis07.row562 (t Basis07.row562)) (add Basis07.row565 Basis07.row566)))))) (add (add (add (add (add node03773 (add node01016 node01348)) (add (add node01487 node03881) (add (t Basis07.row577) node00101))) (add (add (add node00617 Basis07.row583) (add Basis07.row584 Basis07.row585)) (add (add node00343 node00197) (add node04224 Basis07.row593)))) (add (add (add (add (t Basis07.row595) Basis07.row598) (add node02031 Basis07.row602)) (add (add node01746 node02403) (add node01374 Basis07.row609))) (add (add (add node02116 node03342) (add node00602 node00667)) (add (add (t Basis07.row619) Basis07.row620) (add (t Basis07.row621) (t Basis07.row623)))))) (add (add (add (add (add node02754 node02206) (add (t Basis07.row629) Basis07.row631)) (add (add node00384 (t Basis07.row634)) (add (t Basis07.row636) (t Basis07.row640)))) (add (add (add Basis07.row642 Basis07.row646) (add node00672 node01528)) (add (add node00923 Basis07.row653) (add (t Basis07.row654) Basis07.row655)))) (add (add (add (add (t Basis07.row656) Basis07.row660) (add node04338 (t Basis07.row664))) (add (add Basis07.row665 node02456) (add (t Basis07.row667) node03777))) (add (add (add Basis07.row671 (t Basis07.row671)) (add node01270 Basis07.row674)) (add (add Basis07.row676 (t Basis07.row677)) (add node04074 node02525))))))) (add (add (add (add (add (add Basis07.row684 (add (t Basis07.row684) Basis07.row685)) (add (add node02141 node01373) (add Basis07.row693 (t Basis07.row694)))) (add (add (add Basis07.row695 node01489) (add node00186 (t Basis07.row702))) (add (add node03398 Basis07.row705) (add Basis07.row706 Basis07.row708)))) (add (add (add (add Basis07.row709 node00041) (add (t Basis07.row711) Basis07.row714)) (add (add node04320 node02845) (add Basis07.row721 (t Basis07.row721)))) (add (add (add (t Basis07.row725) (t Basis07.row726)) (add Basis07.row727 node01978)) (add (add Basis07.row730 Basis07.row731) (add (t Basis07.row732) node00507))))) (add (add (add (add (add Basis07.row734 Basis07.row735) (add Basis07.row738 (t Basis07.row738))) (add (add node03929 Basis07.row742) (add Basis07.row743 (t Basis07.row745)))) (add (add (add node02579 node01977) (add Basis07.row751 (t Basis07.row751))) (add (add (t Basis07.row752) (t Basis07.row753)) (add node03955 node01669)))) (add (add (add (add (t Basis07.row760) node00797) (add Basis07.row764 (t Basis07.row766))) (add (add node01748 Basis07.row770) (add node01190 (t Basis07.row774)))) (add (add (add Basis07.row777 (t Basis07.row777)) (add (t Basis07.row780) node00700)) (add (add node01465 node01300) (add (t Basis07.row787) node01908)))))) (add (add (add (add (add (add node02015 node02703) (add node02961 Basis07.row797)) (add (add node00925 Basis07.row802) (add Basis07.row803 node02499))) (add (add (add node00281 (t Basis07.row809)) (add node02017 node00986)) (add (add node00411 Basis07.row818) (add (t Basis07.row818) node03854)))) (add (add (add (add node02303 node04239) (add node00685 Basis07.row828)) (add (add node03993 node03969) (add (t Basis07.row834) Basis07.row835))) (add (add (add Basis07.row836 node00355) (add Basis07.row840 node01337)) (add (add node00043 node01314) (add Basis07.row848 node02203))))) (add (add (add (add (add (t Basis07.row851) (t Basis07.row852)) (add (t Basis07.row853) node01221)) (add (add node00624 node01118) (add (t Basis07.row859) node01512))) (add (add (add Basis07.row862 node01119) (add node01574 node04436)) (add (add node01590 Basis07.row872) (add Basis07.row873 (t Basis07.row873))))) (add (add (add (add node01788 Basis07.row877) (add (t Basis07.row877) (t Basis07.row878))) (add (add (t Basis07.row880) Basis07.row881) (add Basis07.row882 Basis07.row883))) (add (add (add node02701 node02089) (add Basis07.row887 node03223)) (add (add node01737 (t Basis07.row892)) (add Basis07.row893 node02709)))))))))

private theorem row182 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 182 (0, 0)) ((rowsAt 10).getD 182 (0, 0)) := by
  apply of_certificate witness182
  · decide +kernel
  · decide +kernel

private noncomputable def witness183 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add (t Basis07.row001) (add (t Basis07.row002) Basis07.row003)) (add (add Basis07.row005 (t Basis07.row007)) (add node01234 (t Basis07.row010)))) (add (add (add (t Basis07.row011) node03360) (add node00190 (t Basis07.row016))) (add (add (t Basis07.row017) node02256) (add Basis07.row021 (t Basis07.row021))))) (add (add (add (t Basis07.row022) (add Basis07.row023 Basis07.row025)) (add (add node00282 node00219) (add node02221 (t Basis07.row033)))) (add (add (add (t Basis07.row034) node04294) (add node01183 node01111)) (add (add node01324 node01475) (add node00115 Basis07.row047))))) (add (add (add (add Basis07.row048 (add node03439 node02690)) (add (add Basis07.row057 node01451) (add node03016 node02402))) (add (add (add node00391 Basis07.row065) (add (t Basis07.row067) Basis07.row069)) (add (add node01943 Basis07.row073) (add (t Basis07.row073) (t Basis07.row075))))) (add (add (add (add node02572 node03131) (add Basis07.row080 (t Basis07.row082))) (add (add node02275 node03098) (add node02042 Basis07.row090))) (add (add (add node00570 (t Basis07.row094)) (add (t Basis07.row096) Basis07.row098)) (add (add Basis07.row101 (t Basis07.row103)) (add node01934 Basis07.row107)))))) (add (add (add (add (add Basis07.row108 (add node01394 node00627)) (add (add node00806 Basis07.row115) (add (t Basis07.row116) Basis07.row117))) (add (add (add node00879 node00693) (add node02732 node01124)) (add (add Basis07.row127 node02606) (add node03130 (t Basis07.row133))))) (add (add (add Basis07.row135 (add node02044 node02632)) (add (add node00736 node02024) (add node02806 Basis07.row148))) (add (add (add (t Basis07.row148) Basis07.row149) (add node02279 (t Basis07.row153))) (add (add Basis07.row154 Basis07.row155) (add Basis07.row156 Basis07.row157))))) (add (add (add (add node01222 (add node03516 node01237)) (add (add Basis07.row166 (t Basis07.row166)) (add node01640 Basis07.row170))) (add (add (add Basis07.row171 node02726) (add (t Basis07.row173) (t Basis07.row174))) (add (add Basis07.row178 Basis07.row179) (add Basis07.row181 node02047)))) (add (add (add (add Basis07.row186 (t Basis07.row187)) (add Basis07.row188 node01705)) (add (add node04483 Basis07.row193) (add (t Basis07.row194) Basis07.row195))) (add (add (add Basis07.row198 node00748) (add Basis07.row204 (t Basis07.row205))) (add (add Basis07.row208 Basis07.row209) (add node02048 node01621))))))) (add (add (add (add (add (add node03434 (add (t Basis07.row219) (t Basis07.row220))) (add (add node04078 Basis07.row224) (add (t Basis07.row228) (t Basis07.row229)))) (add (add (add node01261 node03332) (add node02185 node00678)) (add (add node02312 node01026) (add Basis07.row244 Basis07.row247)))) (add (add (add Basis07.row248 (add node04054 node00014)) (add (add node01464 (t Basis07.row258)) (add node04256 node01341))) (add (add (add Basis07.row264 node03914) (add (t Basis07.row268) node03757)) (add (add node02512 node00272) (add Basis07.row276 (t Basis07.row276)))))) (add (add (add (add node04010 (add Basis07.row281 Basis07.row282)) (add (add node00596 node00501) (add node02510 Basis07.row289))) (add (add (add Basis07.row290 Basis07.row291) (add Basis07.row292 node00628)) (add (add node03373 (t Basis07.row299)) (add Basis07.row301 Basis07.row303)))) (add (add (add (add Basis07.row304 (t Basis07.row304)) (add Basis07.row305 node01207)) (add (add node01769 node02177) (add node03560 (t Basis07.row316)))) (add (add (add node03650 (t Basis07.row320)) (add node00859 node03002)) (add (add node01213 (t Basis07.row328)) (add Basis07.row329 (t Basis07.row330))))))) (add (add (add (add (add Basis07.row332 (add node00163 Basis07.row335)) (add (add (t Basis07.row336) Basis07.row337) (add node01285 (t Basis07.row341)))) (add (add (add Basis07.row342 node00082) (add Basis07.row346 node02099)) (add (add (t Basis07.row351) Basis07.row354) (add (t Basis07.row355) node01267)))) (add (add (add (add (t Basis07.row359) node00182) (add node00612 node02908)) (add (add node00895 node01586) (add node01688 node03594))) (add (add (add node00444 Basis07.row378) (add (t Basis07.row379) node01168)) (add (add node00193 (t Basis07.row383)) (add (t Basis07.row385) Basis07.row387))))) (add (add (add (add node00461 (add node03134 Basis07.row395)) (add (add node01581 (t Basis07.row397)) (add node01224 node00425))) (add (add (add node01713 node01656) (add Basis07.row409 node02188)) (add (add node02922 node01832) (add node01576 node02834)))) (add (add (add (add Basis07.row425 (t Basis07.row425)) (add Basis07.row426 node02377)) (add (add (t Basis07.row429) node03419) (add node02835 (t Basis07.row437)))) (add (add (add node00027 node00259) (add Basis07.row443 Basis07.row444)) (add (add (t Basis07.row444) node01695) (add node03060 node01106)))))))) (add (add (add (add (add (add (add node00209 (add node02073 (t Basis07.row458))) (add (add node01881 node02134) (add node03531 node01418))) (add (add (add node03768 Basis07.row472) (add node00369 node00997)) (add (add node02074 Basis07.row482) (add (t Basis07.row482) node02738)))) (add (add (add (t Basis07.row485) (add node00813 node03734)) (add (add (t Basis07.row491) Basis07.row492) (add Basis07.row493 (t Basis07.row493)))) (add (add (add (t Basis07.row494) (t Basis07.row496)) (add (t Basis07.row497) (t Basis07.row498))) (add (add node02293 Basis07.row504) (add (t Basis07.row505) Basis07.row506))))) (add (add (add (add node01420 (add Basis07.row510 (t Basis07.row511))) (add (add (t Basis07.row512) Basis07.row513) (add Basis07.row516 node01072))) (add (add (add node00125 node03485) (add Basis07.row526 node04240)) (add (add Basis07.row529 (t Basis07.row530)) (add (t Basis07.row531) (t Basis07.row532))))) (add (add (add (add (t Basis07.row533) node01196) (add Basis07.row536 Basis07.row537)) (add (add (t Basis07.row537) node02862) (add node02913 node02601))) (add (add (add node00853 node02801) (add node00943 node04141)) (add (add node01841 Basis07.row555) (add node00933 node01618)))))) (add (add (add (add (add node03354 (add node00002 node02613)) (add (add Basis07.row566 Basis07.row567) (add (t Basis07.row568) node00823))) (add (add (add (t Basis07.row572) node03026) (add (t Basis07.row578) node01197)) (add (add Basis07.row582 (t Basis07.row582)) (add (t Basis07.row585) node00024)))) (add (add (add (add node00800 Basis07.row592) (add (t Basis07.row593) Basis07.row595)) (add (add node03389 Basis07.row600) (add node00322 node02298))) (add (add (add node01278 node01325) (add (t Basis07.row610) Basis07.row611)) (add (add node00965 Basis07.row616) (add node04421 Basis07.row620))))) (add (add (add (add Basis07.row621 (add (t Basis07.row622) (t Basis07.row623))) (add (add node02629 node01205) (add node01191 node00567))) (add (add (add node00384 node03178) (add node01527 (t Basis07.row640))) (add (add node02322 (t Basis07.row643)) (add node00127 node01040)))) (add (add (add (add node02300 Basis07.row651) (add node02061 (t Basis07.row653))) (add (add node02617 node01243) (add Basis07.row661 (t Basis07.row662)))) (add (add (add node00199 node01250) (add (t Basis07.row666) node03777)) (add (add (t Basis07.row670) Basis07.row672) (add (t Basis07.row674) Basis07.row675))))))) (add (add (add (add (add (add (t Basis07.row676) (add node00811 node03928)) (add (add (t Basis07.row682) node03119) (add (t Basis07.row686) Basis07.row687))) (add (add (add Basis07.row688 node02062) (add (t Basis07.row692) (t Basis07.row695))) (add (add Basis07.row696 (t Basis07.row698)) (add node02878 node00957)))) (add (add (add node01735 (add (t Basis07.row705) node01140)) (add (add node03461 node01779) (add node01625 (t Basis07.row717)))) (add (add (add Basis07.row720 node02260) (add node03230 (t Basis07.row724))) (add (add node00233 node00689) (add node00620 node01099))))) (add (add (add (add node01875 (add Basis07.row735 node00061)) (add (add node02615 node01057) (add node01859 node01383))) (add (add (add (t Basis07.row746) node01977) (add node01860 Basis07.row753)) (add (add (t Basis07.row753) (t Basis07.row754)) (add node00788 (t Basis07.row759))))) (add (add (add (add node03462 Basis07.row764) (add Basis07.row765 node02161)) (add (add node00531 Basis07.row772) (add (t Basis07.row773) (t Basis07.row774)))) (add (add (add Basis07.row775 Basis07.row776) (add Basis07.row778 Basis07.row779)) (add (add Basis07.row780 node04028) (add (t Basis07.row783) node00735)))))) (add (add (add (add (add (t Basis07.row787) (add (t Basis07.row788) Basis07.row789)) (add (add (t Basis07.row790) (t Basis07.row791)) (add (t Basis07.row793) (t Basis07.row795)))) (add (add (add Basis07.row796 Basis07.row798) (add node01614 (t Basis07.row801))) (add (add (t Basis07.row803) node02396) (add Basis07.row806 Basis07.row807)))) (add (add (add (add Basis07.row809 node01979) (add node00878 node02672)) (add (add node02219 node01109) (add Basis07.row821 node02303))) (add (add (add node00079 Basis07.row825) (add node00888 (t Basis07.row828))) (add (add (t Basis07.row829) (t Basis07.row832)) (add node01019 node01211))))) (add (add (add (add Basis07.row841 (add Basis07.row842 node00495)) (add (add node02952 Basis07.row849) (add Basis07.row850 Basis07.row851))) (add (add (add (t Basis07.row853) node04291) (add (t Basis07.row858) (t Basis07.row859))) (add (add node00265 node03791) (add node01796 Basis07.row869)))) (add (add (add (add (t Basis07.row869) Basis07.row871) (add Basis07.row872 node01007)) (add (add node00724 node01187) (add Basis07.row879 node02611))) (add (add (add node01038 node00719) (add node00960 (t Basis07.row890))) (add (add Basis07.row891 (t Basis07.row892)) (add (t Basis07.row893) (t Basis07.row894))))))))))

private theorem row183 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 183 (0, 0)) ((rowsAt 10).getD 183 (0, 0)) := by
  apply of_certificate witness183
  · decide +kernel
  · decide +kernel

private noncomputable def witness184 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row051

private theorem row184 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 184 (0, 0)) ((rowsAt 10).getD 184 (0, 0)) := by
  apply of_certificate witness184
  · decide +kernel
  · decide +kernel

private noncomputable def witness185 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add node02678 (add node00776 node03898)) (add (add node01097 (t Basis07.row011)) (add Basis07.row012 node03509))) (add (add (add node00190 node02514) (add node00114 (t Basis07.row023))) (add (add (t Basis07.row024) Basis07.row025) (add node01921 Basis07.row028)))) (add (add (add (t Basis07.row029) (add node02175 node00090)) (add (add node03150 (t Basis07.row039)) (add node00220 node00284))) (add (add (add node01475 (t Basis07.row045)) (add Basis07.row046 Basis07.row047)) (add (add node00357 node03439) (add (t Basis07.row055) node00819))))) (add (add (add (add node01579 (add node04288 Basis07.row064)) (add (add node02654 Basis07.row067) (add Basis07.row068 node00916))) (add (add (add Basis07.row072 (t Basis07.row074)) (add node01174 Basis07.row078)) (add (add (t Basis07.row079) (t Basis07.row081)) (add node02092 node04447)))) (add (add (add (add node02583 (t Basis07.row094)) (add Basis07.row096 Basis07.row097)) (add (add Basis07.row098 Basis07.row099) (add node00074 node01328))) (add (add (add Basis07.row105 node01009) (add node02407 (t Basis07.row110))) (add (add (t Basis07.row111) node01022) (add node02582 (t Basis07.row115))))))) (add (add (add (add (add node01074 (add (t Basis07.row118) node02085)) (add (add node00949 (t Basis07.row124)) (add Basis07.row125 node02586))) (add (add (add (t Basis07.row130) node04167) (add Basis07.row134 (t Basis07.row134))) (add (add node00497 Basis07.row141) (add Basis07.row142 Basis07.row145)))) (add (add (add (t Basis07.row145) (add node02433 node01024)) (add (add node02179 node00161) (add node01762 (t Basis07.row157)))) (add (add (add node03014 node00537) (add node00092 node02859)) (add (add (t Basis07.row166) node00571) (add node03702 node00364))))) (add (add (add (add node01350 (add Basis07.row176 (t Basis07.row177))) (add (add node02046 (t Basis07.row181)) (add Basis07.row182 node00594))) (add (add (add node00498 (t Basis07.row187)) (add node02608 (t Basis07.row191))) (add (add node00549 node01765) (add (t Basis07.row197) Basis07.row198)))) (add (add (add (add node04017 Basis07.row203) (add node01599 Basis07.row210)) (add (add (t Basis07.row211) node00538) (add node02958 (t Basis07.row219)))) (add (add (add node02553 node03328) (add node01858 (t Basis07.row229))) (add (add node01805 node03104) (add Basis07.row235 Basis07.row236))))))) (add (add (add (add (add (add Basis07.row238 (add node02536 node00418)) (add (add node01026 node01994) (add node00783 node01556))) (add (add (add node01891 (t Basis07.row253)) (add node00046 Basis07.row256)) (add (add (t Basis07.row256) Basis07.row258) (add node00397 node02408)))) (add (add (add node02605 (add node03587 Basis07.row269)) (add (add node03757 node02409) (add Basis07.row276 (t Basis07.row276)))) (add (add (add (t Basis07.row278) node01558) (add node00206 node01011)) (add (add node03437 node00540) (add node00694 Basis07.row289))))) (add (add (add (add Basis07.row290 (add node01767 Basis07.row293)) (add (add (t Basis07.row293) node00628) (add Basis07.row297 (t Basis07.row297)))) (add (add (add Basis07.row300 node01288) (add node03970 (t Basis07.row306))) (add (add Basis07.row310 node00150) (add node00868 Basis07.row317)))) (add (add (add (add Basis07.row318 (t Basis07.row319)) (add Basis07.row320 Basis07.row321)) (add (add node02927 (t Basis07.row324)) (add Basis07.row325 node03411))) (add (add (add node03107 node02434) (add (t Basis07.row334) node03495)) (add (add Basis07.row337 Basis07.row339) (add Basis07.row341 node02052)))))) (add (add (add (add (add (t Basis07.row344) (add Basis07.row345 node03891)) (add (add Basis07.row350 node02768) (add node02752 node02231))) (add (add (add (t Basis07.row358) node00182) (add node00725 node04178)) (add (add node01478 Basis07.row372) (add Basis07.row373 Basis07.row375)))) (add (add (add node02313 (add node00793 Basis07.row380)) (add (add node02635 node03632) (add node01562 (t Basis07.row389)))) (add (add (add Basis07.row390 Basis07.row393) (add (t Basis07.row394) (t Basis07.row396))) (add (add node02909 (t Basis07.row400)) (add node03302 node00425))))) (add (add (add (add node01713 (add (t Basis07.row406) (t Basis07.row407))) (add (add node01715 node02188) (add Basis07.row413 (t Basis07.row413)))) (add (add (add node01931 Basis07.row417) (add (t Basis07.row417) node03505)) (add (add node01605 Basis07.row425) (add node04444 Basis07.row428)))) (add (add (add (add Basis07.row429 Basis07.row430) (add Basis07.row433 node03377)) (add (add node01073 (t Basis07.row438)) (add Basis07.row439 node01471))) (add (add (add node03986 node02083) (add node00852 node00828)) (add (add node00931 (t Basis07.row453)) (add node01470 (t Basis07.row458))))))))) (add (add (add (add (add (add (add node00153 (add node02134 node00524)) (add (add node01014 node02809) (add node01838 node01195))) (add (add (add Basis07.row473 node01797) (add node02074 (t Basis07.row478))) (add (add (t Basis07.row479) Basis07.row481) (add node02939 node02391)))) (add (add (add node03451 (add node00885 (t Basis07.row492))) (add (add Basis07.row493 (t Basis07.row493)) (add (t Basis07.row495) node02107))) (add (add (add Basis07.row499 (t Basis07.row499)) (add node02030 (t Basis07.row503))) (add (add node04222 node01276) (add Basis07.row509 Basis07.row510))))) (add (add (add (add node02234 (add node03865 (t Basis07.row516))) (add (add Basis07.row518 node03454) (add node01356 (t Basis07.row522)))) (add (add (add (t Basis07.row525) Basis07.row526) (add (t Basis07.row527) node02108)) (add (add Basis07.row530 node01641) (add Basis07.row534 (t Basis07.row534))))) (add (add (add (add node00383 node02928) (add node03690 (t Basis07.row542))) (add (add node00526 (t Basis07.row545)) (add node01421 (t Basis07.row549)))) (add (add (add Basis07.row551 (t Basis07.row553)) (add (t Basis07.row554) node00933)) (add (add node00029 node01054) (add node04143 Basis07.row566)))))) (add (add (add (add (add node03772 (add (t Basis07.row569) Basis07.row570)) (add (add Basis07.row571 (t Basis07.row571)) (add node02522 node00320))) (add (add (add node02652 Basis07.row579) (add (t Basis07.row579) Basis07.row581)) (add (add Basis07.row583 (t Basis07.row583)) (add (t Basis07.row585) node00024)))) (add (add (add Basis07.row589 (add (t Basis07.row589) node03957)) (add (add node00829 node03310) (add (t Basis07.row597) Basis07.row600))) (add (add (add Basis07.row601 node00344) (add (t Basis07.row604) node01374)) (add (add Basis07.row611 (t Basis07.row612)) (add (t Basis07.row613) node00602))))) (add (add (add (add node02914 (add node03602 node02117)) (add (add node00805 node01431) (add Basis07.row630 (t Basis07.row631)))) (add (add (add node02010 node01117) (add Basis07.row636 (t Basis07.row636))) (add (add (t Basis07.row637) node01983) (add node00305 node02455)))) (add (add (add (add (t Basis07.row643) node04318) (add node00231 (t Basis07.row650))) (add (add (t Basis07.row651) Basis07.row654) (add (t Basis07.row655) Basis07.row658))) (add (add (add node01370 node02196) (add Basis07.row665 node02456)) (add (add node02942 (t Basis07.row672)) (add node01846 node03043))))))) (add (add (add (add (add (add node03079 (add Basis07.row683 (t Basis07.row683))) (add (add (t Basis07.row684) (t Basis07.row686)) (add node00901 Basis07.row691))) (add (add (add node01724 node02823) (add node01423 Basis07.row698)) (add (add node03317 (t Basis07.row704)) (add node03544 (t Basis07.row707))))) (add (add (add node01779 (add node02417 node02174)) (add (add node03399 node01062) (add node01299 Basis07.row723))) (add (add (add Basis07.row724 (t Basis07.row724)) (add node00233 node02542)) (add (add Basis07.row730 node01186) (add node00507 node01867))))) (add (add (add (add (t Basis07.row736) (add node02615 (t Basis07.row740))) (add (add Basis07.row741 Basis07.row742) (add node03123 Basis07.row746))) (add (add (add node01495 node01332) (add node01860 node00673)) (add (add node01850 (t Basis07.row756)) (add (t Basis07.row757) Basis07.row758)))) (add (add (add (add Basis07.row759 node00797) (add (t Basis07.row764) node02421)) (add (add Basis07.row767 node01529) (add Basis07.row771 Basis07.row774))) (add (add (add node01158 (t Basis07.row777)) (add Basis07.row780 node03574)) (add (add node02302 Basis07.row785) (add Basis07.row786 Basis07.row787)))))) (add (add (add (add (add (t Basis07.row788) (add Basis07.row789 (t Basis07.row791))) (add (add (t Basis07.row792) node01909) (add (t Basis07.row795) node01853))) (add (add (add node00925 Basis07.row800) (add Basis07.row802 node00633)) (add (add node04082 (t Basis07.row808)) (add (t Basis07.row809) (t Basis07.row811))))) (add (add (add (t Basis07.row812) (add node00878 Basis07.row815)) (add (add node02602 node00659) (add node00547 node01969))) (add (add (add node03464 (t Basis07.row827)) (add Basis07.row828 (t Basis07.row828))) (add (add Basis07.row831 node04348) (add Basis07.row836 (t Basis07.row836)))))) (add (add (add (add node03787 (add Basis07.row840 node01337)) (add (add node00043 node01854) (add node04430 node02345))) (add (add (add node02018 Basis07.row854) (add node00966 (t Basis07.row856))) (add (add (t Basis07.row858) (t Basis07.row859)) (add Basis07.row861 Basis07.row863)))) (add (add (add (add node01119 node00203) (add (t Basis07.row867) node00569)) (add (add node03793 node01918) (add node01187 node00581))) (add (add (add node00306 Basis07.row881) (add node03409 node00455)) (add (add (t Basis07.row885) Basis07.row889) (add (t Basis07.row889) Basis07.row893)))))))))

private theorem row185 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 185 (0, 0)) ((rowsAt 10).getD 185 (0, 0)) := by
  apply of_certificate witness185
  · decide +kernel
  · decide +kernel

private noncomputable def witness186 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row442

private theorem row186 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 186 (0, 0)) ((rowsAt 10).getD 186 (0, 0)) := by
  apply of_certificate witness186
  · decide +kernel
  · decide +kernel

private noncomputable def witness187 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add node02694 (add (t Basis07.row002) (t Basis07.row003))) (add (add node00606 Basis07.row007) (add Basis07.row008 (t Basis07.row009)))) (add (add (add node00591 (t Basis07.row014)) (add Basis07.row015 node02143)) (add (add node00842 (t Basis07.row024)) (add node02323 Basis07.row028)))) (add (add (add (t Basis07.row028) (add node02175 node02571)) (add (add node01991 node02953) (add node01120 Basis07.row042))) (add (add (add node02034 node00115) (add Basis07.row049 Basis07.row051)) (add (add node02223 node00091) (add node00819 Basis07.row059))))) (add (add (add (add (t Basis07.row061) (add Basis07.row066 (t Basis07.row067))) (add (add node02740 Basis07.row072) (add node03244 node00609))) (add (add (add Basis07.row079 (t Basis07.row080)) (add (t Basis07.row081) (t Basis07.row082))) (add (add node02555 node00992) (add node02042 node01021)))) (add (add (add (add (t Basis07.row091) (t Basis07.row092)) (add node03739 node02636)) (add (add node02310 node00361) (add Basis07.row102 node02788))) (add (add (add node02817 (t Basis07.row108)) (add node01739 node03744)) (add (add Basis07.row114 (t Basis07.row116)) (add Basis07.row118 (t Basis07.row119))))))) (add (add (add (add (add node02846 (add node00170 node01124)) (add (add node00771 (t Basis07.row129)) (add Basis07.row130 node02444))) (add (add (add node00560 Basis07.row138) (add Basis07.row139 Basis07.row140)) (add (add (t Basis07.row140) (t Basis07.row141)) (add node02480 Basis07.row145)))) (add (add (add (add (t Basis07.row145) node03514) (add node02715 (t Basis07.row157))) (add (add Basis07.row158 node03014) (add (t Basis07.row161) (t Basis07.row162)))) (add (add (add (t Basis07.row164) Basis07.row165) (add Basis07.row169 Basis07.row172)) (add (add (t Basis07.row173) Basis07.row176) (add (t Basis07.row177) node02669))))) (add (add (add (add node00239 (add (t Basis07.row184) node01362)) (add (add (t Basis07.row187) node02021) (add Basis07.row192 Basis07.row194))) (add (add (add node01340 node00637) (add node03331 node04443)) (add (add node00765 node01410) (add (t Basis07.row210) node02205)))) (add (add (add (add Basis07.row214 (t Basis07.row215)) (add (t Basis07.row217) Basis07.row220)) (add (add node03639 (t Basis07.row222)) (add Basis07.row224 node02898))) (add (add (add node01274 (t Basis07.row229)) (add node01751 (t Basis07.row233))) (add (add Basis07.row234 Basis07.row238) (add node01708 node00418))))))) (add (add (add (add (add (add (t Basis07.row244) (add (t Basis07.row245) node04372)) (add (add Basis07.row249 node00458) (add Basis07.row251 Basis07.row253))) (add (add (add (t Basis07.row255) node03241) (add Basis07.row258 node00397)) (add (add (t Basis07.row260) (t Basis07.row261)) (add (t Basis07.row262) node02570)))) (add (add (add (t Basis07.row265) (add node03587 Basis07.row269)) (add (add node03757 node02409) (add Basis07.row275 node02796))) (add (add (add node01604 node00301) (add node01894 Basis07.row286)) (add (add (t Basis07.row288) Basis07.row289) (add (t Basis07.row291) node04404))))) (add (add (add (add Basis07.row295 (add (t Basis07.row295) (t Basis07.row297))) (add (add node01110 node01288) (add node00695 node03138))) (add (add (add node01090 node01272) (add node00290 node01208)) (add (add node00867 node04111) (add (t Basis07.row318) (t Basis07.row319))))) (add (add (add (add node03590 (t Basis07.row323)) (add (t Basis07.row324) node01732)) (add (add node00460 node02872) (add node02187 (t Basis07.row335)))) (add (add (add node02622 Basis07.row340) (add (t Basis07.row342) node00597)) (add (add (t Basis07.row346) Basis07.row349) (add (t Basis07.row349) node02596)))))) (add (add (add (add (add Basis07.row353 (add Basis07.row354 node02752)) (add (add Basis07.row356 Basis07.row357) (add node01878 Basis07.row360))) (add (add (add (t Basis07.row360) (t Basis07.row362)) (add Basis07.row363 Basis07.row364)) (add (add node00226 node00482) (add node01478 node00726)))) (add (add (add (add (t Basis07.row374) node02313) (add node00793 node03875)) (add (add node01282 node04058) (add node00981 node02489))) (add (add (add node01999 (t Basis07.row393)) (add node01098 (t Basis07.row399))) (add (add node00720 node02131) (add node01482 node01280))))) (add (add (add (add node00227 (add node01563 node01896)) (add (add (t Basis07.row415) node02413) (add node02103 node00565))) (add (add (add node00173 Basis07.row425) (add node01114 node02707)) (add (add node00552 node01343) (add (t Basis07.row433) node02414)))) (add (add (add (add Basis07.row437 (t Basis07.row437)) (add Basis07.row439 Basis07.row440)) (add (add node00427 node00084) (add Basis07.row445 Basis07.row446))) (add (add (add node03530 Basis07.row450) (add Basis07.row451 (t Basis07.row452))) (add (add node02491 node02210) (add node03205 node01837)))))))) (add (add (add (add (add (add (add (t Basis07.row463) (add node03531 (t Basis07.row468))) (add (add (t Basis07.row470) (t Basis07.row471)) (add (t Basis07.row474) node03630))) (add (add (add (t Basis07.row477) node00341) (add node00738 node02003)) (add (add node03769 node02189) (add (t Basis07.row488) Basis07.row489)))) (add (add (add node03206 (add node03274 Basis07.row496)) (add (add node01445 node00110) (add node02815 Basis07.row502))) (add (add (add node04222 node01985) (add node01420 Basis07.row510)) (add (add Basis07.row512 Basis07.row513) (add node01628 (t Basis07.row516)))))) (add (add (add (add Basis07.row518 (add node03454 Basis07.row521)) (add (add Basis07.row522 (t Basis07.row523)) (add node01840 node00156))) (add (add (add node01641 node00371) (add node02191 Basis07.row537)) (add (add node01232 (t Basis07.row540)) (add Basis07.row541 (t Basis07.row541))))) (add (add (add (add (t Basis07.row543) (t Basis07.row544)) (add node00175 (t Basis07.row546))) (add (add Basis07.row547 node03024) (add node03025 (t Basis07.row554)))) (add (add (add Basis07.row556 node02006) (add (t Basis07.row559) Basis07.row561)) (add (add (t Basis07.row563) (t Basis07.row564)) (add (t Basis07.row565) node04144)))))) (add (add (add (add (add node01775 (add node01487 node03308)) (add (add Basis07.row577 Basis07.row580) (add Basis07.row581 node01458))) (add (add (add (t Basis07.row583) Basis07.row586) (add Basis07.row588 node00800)) (add (add (t Basis07.row591) node02452) (add (t Basis07.row595) Basis07.row596)))) (add (add (add (add Basis07.row597 Basis07.row598) (add (t Basis07.row598) node01803)) (add (add Basis07.row601 (t Basis07.row601)) (add node00722 Basis07.row606))) (add (add (add node00025 node00815) (add node03342 node00602)) (add (add node02347 Basis07.row620) (add node00184 (t Basis07.row624)))))) (add (add (add (add node02915 (add node01466 Basis07.row630)) (add (add Basis07.row632 Basis07.row633) (add node00469 node04157))) (add (add (add (t Basis07.row638) (t Basis07.row639)) (add Basis07.row640 node01000)) (add (add node00914 Basis07.row645) (add Basis07.row646 node03815)))) (add (add (add (add node00974 node02038) (add node01078 node00831)) (add (add (t Basis07.row658) (t Basis07.row659)) (add node01018 node02196))) (add (add (add (t Basis07.row663) Basis07.row664) (add Basis07.row667 (t Basis07.row667))) (add (add Basis07.row671 (t Basis07.row671)) (add node02497 Basis07.row674))))))) (add (add (add (add (add (add Basis07.row675 (add Basis07.row676 (t Basis07.row678))) (add (add Basis07.row682 (t Basis07.row682)) (add node01926 Basis07.row687))) (add (add (add node01750 (t Basis07.row690)) (add Basis07.row692 node04385)) (add (add Basis07.row695 node02078) (add (t Basis07.row698) Basis07.row699)))) (add (add (add Basis07.row700 (add Basis07.row701 (t Basis07.row701))) (add (add node00128 node02462) (add (t Basis07.row711) (t Basis07.row712)))) (add (add (add Basis07.row713 (t Basis07.row715)) (add node00578 node02845)) (add (add node02339 (t Basis07.row722)) (add Basis07.row725 (t Basis07.row726)))))) (add (add (add (add node00689 (add node01694 (t Basis07.row731))) (add (add Basis07.row733 node03724) (add node02301 node01057))) (add (add (add node04425 node03167) (add node02564 node01332)) (add (add node01860 node02764) (add node03033 Basis07.row759)))) (add (add (add (add node00797 node01492) (add node02467 Basis07.row769)) (add (add node04150 node03228) (add (t Basis07.row777) node00711))) (add (add (add node04428 node01465) (add Basis07.row785 Basis07.row786)) (add (add Basis07.row787 Basis07.row788) (add Basis07.row789 Basis07.row790)))))) (add (add (add (add (add Basis07.row791 (add node00279 node02918)) (add (add Basis07.row797 (t Basis07.row799)) (add node02777 node01989))) (add (add (add node02268 Basis07.row808) (add Basis07.row809 (t Basis07.row810))) (add (add node02645 (t Basis07.row813)) (add node00411 node01531)))) (add (add (add (add node01081 node00919) (add Basis07.row822 node03938)) (add (add node03220 (t Basis07.row828)) (add node00144 node00958))) (add (add (add node01910 Basis07.row835) (add Basis07.row836 (t Basis07.row836))) (add (add (t Basis07.row837) Basis07.row839) (add Basis07.row840 node00590))))) (add (add (add (add Basis07.row843 (add node02214 node01672)) (add (add Basis07.row849 node00413) (add node00189 node01572))) (add (add (add node00675 node03047) (add node00265 Basis07.row863)) (add (add node01020 node01397) (add node01796 Basis07.row869)))) (add (add (add (add Basis07.row870 node02389) (add Basis07.row875 node02304)) (add (add (t Basis07.row878) node03074) (add (t Basis07.row881) node00877))) (add (add (add node00455 Basis07.row886) (add (t Basis07.row886) Basis07.row887)) (add (add node01193 node00235) (add node02603 node01970)))))))))

private theorem row187 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 187 (0, 0)) ((rowsAt 10).getD 187 (0, 0)) := by
  apply of_certificate witness187
  · decide +kernel
  · decide +kernel

private noncomputable def witness188 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add node02678 (add Basis07.row002 node00926)) (add (add (t Basis07.row007) node01757) (add node02867 node00990))) (add (add (add Basis07.row019 node02702) (add Basis07.row024 Basis07.row026)) (add (add (t Basis07.row026) node03290) (add node02175 Basis07.row037)))) (add (add (add (add Basis07.row038 (t Basis07.row039)) (add Basis07.row041 node02040)) (add (add node02357 node03249) (add Basis07.row048 node02211))) (add (add (add node00358 node01594) (add node00091 node00819)) (add (add node03291 (t Basis07.row062)) (add (t Basis07.row063) Basis07.row064))))) (add (add (add (add node01375 (add Basis07.row067 Basis07.row068)) (add (add node03191 node00608) (add node03244 (t Basis07.row076)))) (add (add (add node03131 (t Basis07.row082)) (add Basis07.row083 node02092)) (add (add node00377 (t Basis07.row089)) (add node02225 node00775)))) (add (add (add (add node01336 (t Basis07.row097)) (add (t Basis07.row099) Basis07.row101)) (add (add Basis07.row102 node00753) (add node02689 Basis07.row106))) (add (add (add node03562 (t Basis07.row109)) (add (t Basis07.row110) node00627)) (add (add Basis07.row112 node01993) (add node03366 node00879)))))) (add (add (add (add (add node02681 (add (t Basis07.row122) node00945)) (add (add node02648 Basis07.row129) (add node00075 (t Basis07.row132)))) (add (add (add Basis07.row133 node03367) (add node00497 node01430)) (add (add node01514 (t Basis07.row143)) (add node02171 Basis07.row147)))) (add (add (add (add node00379 node02095) (add Basis07.row152 (t Basis07.row154))) (add (add node01647 Basis07.row158) (add Basis07.row159 node00018))) (add (add (add node00537 node00950) (add node00180 node01226)) (add (add node00380 node04206) (add Basis07.row172 Basis07.row173))))) (add (add (add (add (add node00584 node03961) (add (t Basis07.row178) (t Basis07.row179))) (add (add (t Basis07.row181) (t Basis07.row183)) (add Basis07.row184 Basis07.row186))) (add (add (add Basis07.row188 node02608) (add (t Basis07.row192) node02354)) (add (add (t Basis07.row195) (t Basis07.row196)) (add (t Basis07.row198) (t Basis07.row201))))) (add (add (add (add Basis07.row203 Basis07.row204) (add node00252 (t Basis07.row207))) (add (add node01633 node01349) (add Basis07.row214 node02717))) (add (add (add Basis07.row218 (t Basis07.row218)) (add node01953 Basis07.row223)) (add (add (t Basis07.row223) Basis07.row224) (add node03278 Basis07.row228))))))) (add (add (add (add (add (add node00224 (add node01751 node03332)) (add (add node00395 (t Basis07.row237)) (add Basis07.row239 (t Basis07.row241)))) (add (add (add Basis07.row243 node00011) (add node02609 node04054)) (add (add node00750 Basis07.row254) (add Basis07.row256 node00679)))) (add (add (add (add node02570 node03737) (add (t Basis07.row267) (t Basis07.row268))) (add (add (t Basis07.row269) (t Basis07.row271)) (add node02513 (t Basis07.row274)))) (add (add (add Basis07.row275 node03255) (add (t Basis07.row278) Basis07.row280)) (add (add Basis07.row281 node03500) (add Basis07.row285 (t Basis07.row285)))))) (add (add (add (add Basis07.row287 (add Basis07.row288 node02502)) (add (add (t Basis07.row291) Basis07.row292) (add Basis07.row293 Basis07.row295))) (add (add (add (t Basis07.row295) node03866) (add Basis07.row299 (t Basis07.row300))) (add (add node00695 node00792) (add node01207 node03619)))) (add (add (add (add node02474 (t Basis07.row311)) (add node00867 node00834)) (add (add node01047 node02938) (add (t Basis07.row322) Basis07.row324))) (add (add (add node03200 node00460) (add Basis07.row330 node03797)) (add (add node02187 Basis07.row336) (add node00773 node02098)))))) (add (add (add (add (add (t Basis07.row343) (add node02220 (t Basis07.row346))) (add (add Basis07.row348 node02100) (add node00109 (t Basis07.row353)))) (add (add (add node01267 (t Basis07.row359)) (add node00844 (t Basis07.row364))) (add (add Basis07.row366 Basis07.row367) (add Basis07.row368 node01688)))) (add (add (add (add Basis07.row372 Basis07.row374) (add node02313 node00256)) (add (add Basis07.row379 Basis07.row380) (add (t Basis07.row380) node01655))) (add (add (add node03766 node00194) (add node00312 Basis07.row390)) (add (add node01999 Basis07.row395) (add node00763 Basis07.row398))))) (add (add (add (add (add (t Basis07.row399) (t Basis07.row400)) (add (t Basis07.row401) Basis07.row402)) (add (add Basis07.row403 node02131) (add Basis07.row406 node02737))) (add (add (add node01280 node02102) (add node00337 node01896)) (add (add node00721 Basis07.row419) (add (t Basis07.row419) (t Basis07.row421))))) (add (add (add (add Basis07.row422 node03111) (add node02988 (t Basis07.row429))) (add (add (t Basis07.row432) node04411) (add (t Basis07.row436) node00027))) (add (add (add node02520 node00681) (add (t Basis07.row445) node02767)) (add (add node03569 node00931) (add node01379 Basis07.row456)))))))) (add (add (add (add (add (add (add (t Basis07.row456) (add node03468 Basis07.row461)) (add (add Basis07.row462 node04064) (add (t Basis07.row466) (t Basis07.row467)))) (add (add (add Basis07.row468 node04346) (add Basis07.row473 Basis07.row474)) (add (add (t Basis07.row475) node00317) (add node00525 node01185)))) (add (add (add (add node03287 node01395) (add (t Basis07.row488) (t Basis07.row489))) (add (add (t Basis07.row490) node04006) (add (t Basis07.row494) (t Basis07.row495)))) (add (add (add (t Basis07.row496) node02293) (add (t Basis07.row503) node01582)) (add (add Basis07.row507 node01310) (add node00403 (t Basis07.row512)))))) (add (add (add (add node00174 (add node01628 Basis07.row517)) (add (add Basis07.row518 (t Basis07.row518)) (add Basis07.row519 (t Basis07.row520)))) (add (add (add (t Basis07.row522) Basis07.row526) (add (t Basis07.row526) (t Basis07.row530))) (add (add node00086 Basis07.row534) (add (t Basis07.row534) node02311)))) (add (add (add (add (t Basis07.row537) Basis07.row538) (add (t Basis07.row540) node02110)) (add (add Basis07.row545 (t Basis07.row545)) (add node03770 node00165))) (add (add (add node04007 Basis07.row555) (add node00933 node01618)) (add (add node00934 Basis07.row561) (add (t Basis07.row563) node01258)))))) (add (add (add (add (add node00890 (add (t Basis07.row569) Basis07.row570)) (add (add node01775 Basis07.row573) (add node00898 node01568))) (add (add (add node01197 node01608) (add (t Basis07.row583) (t Basis07.row584))) (add (add (t Basis07.row585) node01429) (add node00973 node03489)))) (add (add (add (add node00810 node00158) (add (t Basis07.row596) node02217)) (add (add node00722 node02653) (add node01325 (t Basis07.row608)))) (add (add (add node02116 Basis07.row616) (add Basis07.row617 (t Basis07.row619))) (add (add Basis07.row620 Basis07.row621) (add (t Basis07.row622) node01643))))) (add (add (add (add (add node00468 (t Basis07.row630)) (add node01844 node01179)) (add (add node00904 Basis07.row637) (add node01685 Basis07.row640))) (add (add (add node00835 node00914) (add Basis07.row645 (t Basis07.row645))) (add (add Basis07.row647 Basis07.row652) (add node01778 node01845)))) (add (add (add (add node01370 (t Basis07.row660)) (add Basis07.row662 (t Basis07.row662))) (add (add node01156 node02741) (add (t Basis07.row667) node03163))) (add (add (add (t Basis07.row671) Basis07.row672) (add Basis07.row673 (t Basis07.row674))) (add (add (t Basis07.row675) node00185) (add (t Basis07.row677) (t Basis07.row679)))))))) (add (add (add (add (add (add Basis07.row681 (add (t Basis07.row682) node00795)) (add (add node00734 node04168) (add node00008 (t Basis07.row692)))) (add (add (add node03008 node01489) (add node01085 node03435)) (add (add node01570 node00324) (add node01927 (t Basis07.row707))))) (add (add (add (add Basis07.row709 (t Basis07.row709)) (add Basis07.row711 Basis07.row712)) (add (add (t Basis07.row713) (t Basis07.row714)) (add node04320 node00632))) (add (add (add node00142 node01299) (add node01611 (t Basis07.row724))) (add (add node01141 node00689) (add Basis07.row730 node01099))))) (add (add (add (add Basis07.row733 (add Basis07.row734 Basis07.row736)) (add (add node00216 node01780) (add Basis07.row742 node01182))) (add (add (add node02362 node02305) (add node01332 (t Basis07.row750))) (add (add node00673 node01473) (add node00788 node00352)))) (add (add (add (add node01384 (t Basis07.row760)) (add Basis07.row761 Basis07.row762)) (add (add (t Basis07.row762) (t Basis07.row765)) (add Basis07.row766 node02013))) (add (add (add (t Basis07.row769) Basis07.row771) (add Basis07.row772 node00389)) (add (add (t Basis07.row775) Basis07.row776) (add node00785 (t Basis07.row778))))))) (add (add (add (add (add (t Basis07.row779) (add (t Basis07.row780) (t Basis07.row782))) (add (add (t Basis07.row784) node02142) (add node04380 node02173))) (add (add (add node00279 (t Basis07.row795)) (add node00568 node00743)) (add (add Basis07.row800 Basis07.row801) (add node02359 Basis07.row805)))) (add (add (add (add node03853 (t Basis07.row810)) (add (t Basis07.row811) (t Basis07.row812))) (add (add node00218 node02343) (add Basis07.row817 Basis07.row818))) (add (add (add Basis07.row820 (t Basis07.row821)) (add (t Basis07.row822) node04236)) (add (add Basis07.row828 Basis07.row829) (add node03993 node00494))))) (add (add (add (add (add node02925 (t Basis07.row835)) (add node03221 (t Basis07.row841))) (add (add node00975 node00412) (add node01216 node01630))) (add (add (add node02018 node00623) (add node00864 node01786)) (add (add Basis07.row862 node03323) (add Basis07.row865 (t Basis07.row868))))) (add (add (add (add (t Basis07.row869) Basis07.row872) (add node01007 node01264)) (add (add node01002 node00581) (add Basis07.row879 node03408))) (add (add (add node03410 node00959) (add node01249 node01193)) (add (add node01738 Basis07.row892) (add Basis07.row893 node01674)))))))))

private theorem row188 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 188 (0, 0)) ((rowsAt 10).getD 188 (0, 0)) := by
  apply of_certificate witness188
  · decide +kernel
  · decide +kernel

private noncomputable def witness189 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row052

private theorem row189 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 189 (0, 0)) ((rowsAt 10).getD 189 (0, 0)) := by
  apply of_certificate witness189
  · decide +kernel
  · decide +kernel

private noncomputable def witness190 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row452

private theorem row190 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 190 (0, 0)) ((rowsAt 10).getD 190 (0, 0)) := by
  apply of_certificate witness190
  · decide +kernel
  · decide +kernel

private noncomputable def witness191 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add node01884 (add node00776 node01939)) (add (add (t Basis07.row007) (t Basis07.row008)) (add node01886 Basis07.row014))) (add (add (add node02932 (t Basis07.row017)) (add (t Basis07.row018) node01385)) (add (add Basis07.row022 Basis07.row023) (add Basis07.row026 (t Basis07.row026))))) (add (add (add node00818 (add node00376 (t Basis07.row031))) (add (add (t Basis07.row032) Basis07.row033) (add node01744 Basis07.row037))) (add (add (add Basis07.row038 node00133) (add Basis07.row040 node02309)) (add (add node01699 node03493) (add Basis07.row048 (t Basis07.row049)))))) (add (add (add (add node02665 (add node01644 Basis07.row054)) (add (add node01302 node01579) (add Basis07.row060 (t Basis07.row061)))) (add (add (add (t Basis07.row062) Basis07.row063) (add (t Basis07.row065) node00001)) (add (add Basis07.row069 node03751) (add node01174 Basis07.row077)))) (add (add (add (add Basis07.row080 node02066) (add Basis07.row083 node03250)) (add (add node00476 node00511) (add Basis07.row091 Basis07.row092))) (add (add (add node00775 node01336) (add node00360 Basis07.row101)) (add (add node02822 node00592) (add (t Basis07.row107) (t Basis07.row108))))))) (add (add (add (add (add Basis07.row109 (add node00237 node01022)) (add (add node00478 node04289) (add node02443 (t Basis07.row120)))) (add (add (add (t Basis07.row121) node00949) (add node00945 (t Basis07.row125))) (add (add node00649 node00075) (add Basis07.row132 node00843)))) (add (add (add node02935 (add node03954 (t Basis07.row139))) (add (add node01883 node02479) (add (t Basis07.row145) (t Basis07.row146)))) (add (add (add (t Basis07.row148) node03514) (add (t Basis07.row151) node01704)) (add (add node03584 node01237) (add (t Basis07.row167) Basis07.row168))))) (add (add (add (add node00977 (add (t Basis07.row171) (t Basis07.row172))) (add (add node02515 (t Basis07.row175)) (add node02706 Basis07.row179))) (add (add (add (t Basis07.row180) (t Basis07.row181)) (add (t Basis07.row182) Basis07.row183)) (add (add node02137 Basis07.row186) (add node00766 (t Basis07.row191))))) (add (add (add (add Basis07.row192 node00240) (add node01363 node02432)) (add (add Basis07.row200 Basis07.row202) (add node00192 (t Basis07.row205)))) (add (add (add Basis07.row207 (t Basis07.row207)) (add node00108 node02852)) (add (add (t Basis07.row216) Basis07.row219) (add (t Basis07.row219) node01600))))))) (add (add (add (add (add (add node00066 (add node00094 (t Basis07.row226))) (add (add node01274 (t Basis07.row229)) (add Basis07.row232 node00289))) (add (add (add (t Basis07.row235) Basis07.row236) (add node02358 node02536)) (add (add node00418 node00978) (add node01994 node01066)))) (add (add (add node01996 (add node02446 node03275)) (add (add node02559 Basis07.row261) (add node01518 node00500))) (add (add (add node03055 Basis07.row270) (add node00058 Basis07.row272)) (add (add (t Basis07.row274) Basis07.row276) (add Basis07.row277 (t Basis07.row277)))))) (add (add (add (add node02537 (add (t Basis07.row280) Basis07.row281)) (add (add node03649 node00501) (add node00255 node02051))) (add (add (add (t Basis07.row292) node04476) (add Basis07.row296 node01100)) (add (add node00639 node02871) (add (t Basis07.row305) (t Basis07.row306))))) (add (add (add (add node00047 node00737) (add node01208 Basis07.row314)) (add (add Basis07.row315 Basis07.row316) (add node01047 node03504))) (add (add (add node00151 node03002) (add (t Basis07.row326) node00460)) (add (add node00883 (t Basis07.row332)) (add (t Basis07.row333) Basis07.row335)))))) (add (add (add (add (add (t Basis07.row335) (add Basis07.row337 node02622)) (add (add Basis07.row340 node00731) (add Basis07.row345 Basis07.row346))) (add (add (add node00302 Basis07.row351) (add node02920 node00611)) (add (add node00077 node00563) (add (t Basis07.row360) (t Basis07.row361))))) (add (add (add (add node00725 node00122) (add (t Basis07.row365) (t Basis07.row366))) (add (add node00083 node04044) (add node01342 node03095))) (add (add (add node00097 node00336) (add node02427 (t Basis07.row389))) (add (add node01999 (t Basis07.row393)) (add node02376 Basis07.row397))))) (add (add (add (add (t Basis07.row397) (add node03524 node00869)) (add (add node02708 (t Basis07.row404)) (add (t Basis07.row409) node00227))) (add (add (add node02412 node02910) (add node02413 Basis07.row419)) (add (add (t Basis07.row420) (t Basis07.row421)) (add node03596 node00098)))) (add (add (add (add (t Basis07.row427) node01403) (add node00338 Basis07.row433)) (add (add node00138 node01897) (add node02719 node01471))) (add (add (add node01061 (t Basis07.row445)) (add node02911 node04110)) (add (add Basis07.row452 (t Basis07.row452)) (add (t Basis07.row454) Basis07.row456)))))))) (add (add (add (add (add (add (add (t Basis07.row456) (add (t Basis07.row458) (t Basis07.row459))) (add (add (t Basis07.row460) node02333) (add node00464 node03845))) (add (add (add Basis07.row467 node01093) (add node02802 node00884)) (add (add (t Basis07.row477) Basis07.row479) (add (t Basis07.row479) Basis07.row481)))) (add (add (add Basis07.row482 (add (t Basis07.row482) (t Basis07.row483))) (add (add Basis07.row485 (t Basis07.row486)) (add Basis07.row488 Basis07.row489))) (add (add (add (t Basis07.row490) node03160) (add node02107 Basis07.row499)) (add (add (t Basis07.row501) Basis07.row502) (add Basis07.row503 node02990))))) (add (add (add (add node00448 (add Basis07.row508 (t Basis07.row509))) (add (add node01368 (t Basis07.row512)) (add (t Basis07.row513) node00210))) (add (add (add node03187 (t Basis07.row518)) (add (t Basis07.row519) node01356)) (add (add node03049 Basis07.row527) (add (t Basis07.row527) (t Basis07.row528))))) (add (add (add (add (t Basis07.row529) node01281) (add (t Basis07.row533) node02191)) (add (add node03721 Basis07.row540) (add (t Basis07.row541) Basis07.row545))) (add (add (add node01052 node02705) (add node03025 (t Basis07.row553))) (add (add Basis07.row556 node02296) (add node04361 node01181)))))) (add (add (add (add (add Basis07.row564 (add (t Basis07.row564) node01962)) (add (add Basis07.row570 (t Basis07.row570)) (add node02522 node03180))) (add (add (add node00070 node01197) (add node02072 Basis07.row583)) (add (add (t Basis07.row585) Basis07.row586) (add node01971 (t Basis07.row591))))) (add (add (add (add Basis07.row592 Basis07.row594) (add node03432 node00276)) (add (add Basis07.row602 (t Basis07.row602)) (add Basis07.row605 Basis07.row606))) (add (add (add node01325 (t Basis07.row608)) (add node00033 node00965)) (add (add node02562 node02691) (add (t Basis07.row617) node02957))))) (add (add (add (add node01263 (add node03188 (t Basis07.row628))) (add (add node01610 (t Basis07.row633)) (add node01179 node04465))) (add (add (add node00305 node01697) (add Basis07.row644 node01963)) (add (add Basis07.row647 (t Basis07.row647)) (add node02300 (t Basis07.row650))))) (add (add (add (add node04452 Basis07.row656) (add Basis07.row658 Basis07.row659)) (add (add Basis07.row660 node01201) (add (t Basis07.row663) Basis07.row664))) (add (add (add node03458 (t Basis07.row669)) (add Basis07.row670 Basis07.row671)) (add (add (t Basis07.row671) node01543) (add (t Basis07.row674) Basis07.row675))))))) (add (add (add (add (add (add node00185 (add node01079 node00347)) (add (add node01496 node00053) (add node03459 node00214))) (add (add (add Basis07.row693 (t Basis07.row693)) (add Basis07.row695 node01580)) (add (add Basis07.row699 (t Basis07.row700)) (add (t Basis07.row702) (t Basis07.row703))))) (add (add (add node00324 (add node02198 node02158)) (add (add node00874 Basis07.row711) (add Basis07.row712 Basis07.row713))) (add (add (add node00006 node00578) (add node00632 Basis07.row719)) (add (add (t Basis07.row720) (t Basis07.row721)) (add node02133 node03013))))) (add (add (add (add Basis07.row727 (add node02244 (t Basis07.row729))) (add (add (t Basis07.row730) node01186) (add (t Basis07.row734) Basis07.row735))) (add (add (add node00061 (t Basis07.row737)) (add (t Basis07.row738) node02544)) (add (add node01080 node01383) (add node00003 Basis07.row750)))) (add (add (add (add (t Basis07.row751) node01473) (add (t Basis07.row756) node01782)) (add (add (t Basis07.row763) node02421) (add Basis07.row767 (t Basis07.row769)))) (add (add (add Basis07.row770 (t Basis07.row771)) (add node01142 (t Basis07.row776))) (add (add node00004 (t Basis07.row779)) (add node03732 node00103)))))) (add (add (add (add (add node02270 (add node00390 node01908)) (add (add node01548 Basis07.row792) (add node02594 node01852))) (add (add (add node03401 node01784) (add node02268 Basis07.row808)) (add (add Basis07.row809 Basis07.row810) (add (t Basis07.row810) (t Basis07.row811))))) (add (add (add (add Basis07.row812 Basis07.row814) (add (t Basis07.row814) node01509)) (add (add node03936 Basis07.row821) (add node02252 node03464))) (add (add (add node00685 Basis07.row827) (add (t Basis07.row828) node03855)) (add (add node03084 node03141) (add node04153 node01211))))) (add (add (add (add node02422 (add node00975 node01854)) (add (add node01672 Basis07.row849) (add Basis07.row851 Basis07.row853))) (add (add (add (t Basis07.row855) node02948) (add (t Basis07.row859) Basis07.row860)) (add (add Basis07.row862 node00203) (add Basis07.row867 (t Basis07.row868))))) (add (add (add (add node02884 Basis07.row871) (add (t Basis07.row871) node00724)) (add (add Basis07.row876 (t Basis07.row876)) (add node03578 Basis07.row881))) (add (add (add node02611 node00455) (add Basis07.row887 Basis07.row888)) (add (add Basis07.row890 Basis07.row891) (add node00169 (t Basis07.row895))))))))))

private theorem row191 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 191 (0, 0)) ((rowsAt 10).getD 191 (0, 0)) := by
  apply of_certificate witness191
  · decide +kernel
  · decide +kernel

private noncomputable def witness192 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add (t Basis07.row000) (add Basis07.row002 (t Basis07.row004))) (add (add (t Basis07.row005) node01102) (add node00415 Basis07.row011))) (add (add (add node03247 Basis07.row015) (add node04202 node02256)) (add (add node00842 Basis07.row022) (add Basis07.row023 node00918)))) (add (add (add (add node00282 node03290) (add Basis07.row030 Basis07.row032)) (add (add (t Basis07.row033) (t Basis07.row034)) (add (t Basis07.row035) node01122))) (add (add (add node00081 node01183) (add (t Basis07.row040) Basis07.row041)) (add (add node01324 (t Basis07.row044)) (add Basis07.row046 node00626))))) (add (add (add (add (t Basis07.row049) (add (t Basis07.row051) (t Basis07.row052))) (add (add node01817 (t Basis07.row055)) (add node00072 node01578))) (add (add (add node03364 node01703) (add node01375 (t Basis07.row067))) (add (add (t Basis07.row068) (t Basis07.row069)) (add (t Basis07.row070) node00269)))) (add (add (add (add (t Basis07.row072) Basis07.row075) (add (t Basis07.row076) (t Basis07.row078))) (add (add node00134 Basis07.row081) (add Basis07.row082 node00135))) (add (add (add node02086 node02813) (add (t Basis07.row089) Basis07.row091)) (add (add Basis07.row092 node03753) (add Basis07.row097 node02478)))))) (add (add (add (add (add Basis07.row100 (add (t Basis07.row100) node01934)) (add (add (t Basis07.row107) (t Basis07.row108)) (add node00222 (t Basis07.row113)))) (add (add (add (t Basis07.row114) Basis07.row118) (add (t Basis07.row118) (t Basis07.row120))) (add (add node01242 node00170) (add node01124 (t Basis07.row125))))) (add (add (add (add (t Basis07.row126) (t Basis07.row127)) (add (t Basis07.row128) node03130)) (add (add node00010 Basis07.row134) (add (t Basis07.row135) Basis07.row136))) (add (add (add Basis07.row138 (t Basis07.row138)) (add (t Basis07.row139) Basis07.row143)) (add (add (t Basis07.row145) Basis07.row147) (add Basis07.row148 node01024))))) (add (add (add (add (t Basis07.row150) (add node01704 Basis07.row155)) (add (add node01949 Basis07.row158) (add Basis07.row159 (t Basis07.row159)))) (add (add (add node01890 node01165) (add Basis07.row165 node01226)) (add (add node00571 node02851) (add Basis07.row173 (t Basis07.row173))))) (add (add (add (add Basis07.row177 node01823) (add Basis07.row181 (t Basis07.row182))) (add (add (t Basis07.row183) Basis07.row184) (add Basis07.row185 Basis07.row186))) (add (add (add Basis07.row187 Basis07.row190) (add node00162 node00271)) (add (add (t Basis07.row194) node02530) (add Basis07.row197 Basis07.row198))))))) (add (add (add (add (add (add node00251 (add node00748 node01387)) (add (add Basis07.row205 node01599) (add node00223 (t Basis07.row210)))) (add (add (add node01952 node00538) (add node01172 node00595)) (add (add node01452 Basis07.row220) (add Basis07.row221 node01824)))) (add (add (add (add Basis07.row224 node02558) (add node00076 node00224)) (add (add node01805 node00663) (add Basis07.row236 (t Basis07.row238)))) (add (add (add Basis07.row239 Basis07.row240) (add node03371 Basis07.row244)) (add (add Basis07.row245 node02673) (add (t Basis07.row250) node00750))))) (add (add (add (add node01464 (add node00679 node01341)) (add (add node01892 (t Basis07.row268)) (add Basis07.row271 Basis07.row272))) (add (add (add node03915 node03629) (add node02604 node03885)) (add (add node00894 Basis07.row288) (add node02051 (t Basis07.row291))))) (add (add (add (add (t Basis07.row292) node00921) (add Basis07.row295 node03226)) (add (add node00022 (t Basis07.row302)) (add (t Basis07.row303) Basis07.row307))) (add (add (add Basis07.row312 node04130) (add node01047 node01192)) (add (add (t Basis07.row320) (t Basis07.row321)) (add (t Basis07.row323) (t Basis07.row324))))))) (add (add (add (add (add node02697 (add node03035 node00541)) (add (add Basis07.row331 Basis07.row332) (add Basis07.row333 Basis07.row334))) (add (add (add Basis07.row335 (t Basis07.row335)) (add Basis07.row337 Basis07.row339)) (add (add (t Basis07.row340) (t Basis07.row342)) (add node01309 node01935)))) (add (add (add (add node02596 node00987) (add node00611 node01416)) (add (add Basis07.row361 node00612) (add node03499 (t Basis07.row365)))) (add (add (add (t Basis07.row366) node04406) (add node01389 (t Basis07.row374))) (add (add Basis07.row375 Basis07.row376) (add (t Basis07.row376) Basis07.row378))))) (add (add (add (add (add (t Basis07.row378) node00896) (add Basis07.row383 (t Basis07.row383))) (add (add Basis07.row385 node00981) (add node00312 node01999))) (add (add (add Basis07.row394 (t Basis07.row394)) (add node00763 Basis07.row398)) (add (add node00123 Basis07.row402) (add Basis07.row403 (t Basis07.row403))))) (add (add (add (add node00445 node01679) (add Basis07.row413 Basis07.row414)) (add (add Basis07.row415 Basis07.row416) (add (t Basis07.row416) (t Basis07.row417)))) (add (add (add (t Basis07.row418) (t Basis07.row419)) (add node01510 Basis07.row424)) (add (add node03656 Basis07.row428) (add node04410 node00586)))))))) (add (add (add (add (add (add (add node00027 (add node02504 node03425)) (add (add node01689 node04455) (add (t Basis07.row449) Basis07.row450))) (add (add (add Basis07.row451 node01106) (add node02491 node02210)) (add (add node03468 Basis07.row460) (add (t Basis07.row462) node03450)))) (add (add (add (add node00340 Basis07.row470) (add node00485 node00368)) (add (add node01797 node00317) (add (t Basis07.row478) node02710))) (add (add (add node00154 node04457) (add node00155 node01051)) (add (add node02495 (t Basis07.row491)) (add node01138 node01293))))) (add (add (add (add node02292 (add (t Basis07.row498) Basis07.row501)) (add (add (t Basis07.row503) (t Basis07.row504)) (add Basis07.row505 node01276))) (add (add (add (t Basis07.row508) node02450) (add node00017 node02378)) (add (add (t Basis07.row515) node01015) (add node00505 (t Basis07.row519))))) (add (add (add (add Basis07.row520 node00125) (add (t Basis07.row522) Basis07.row523)) (add (add node03062 node01134) (add Basis07.row529 node02876))) (add (add (add node02720 node00078) (add Basis07.row536 (t Basis07.row537))) (add (add Basis07.row539 node00998) (add (t Basis07.row544) node03012)))))) (add (add (add (add (add node00195 (add Basis07.row549 node00449)) (add (add node01566 Basis07.row556) (add (t Basis07.row556) node02006))) (add (add (add (t Basis07.row560) node02169) (add (t Basis07.row563) node02318)) (add (add node03224 Basis07.row570) (add node01486 node03774)))) (add (add (add (add (t Basis07.row578) Basis07.row579) (add node01458 Basis07.row585)) (add (add (t Basis07.row585) Basis07.row586) (add node02008 node04371))) (add (add (add (t Basis07.row594) node00158) (add node01524 node00276)) (add (add node01629 node01278) (add node00779 node02115))))) (add (add (add (add (add node00794 node00873) (add node02454 (t Basis07.row618))) (add (add node00184 (t Basis07.row623)) (add Basis07.row624 Basis07.row625))) (add (add (add Basis07.row626 node00468) (add (t Basis07.row631) (t Basis07.row632))) (add (add (t Basis07.row634) (t Basis07.row636)) (add node01983 node02165)))) (add (add (add (add (t Basis07.row643) node00406) (add node00672 node01528)) (add (add node00974 Basis07.row652) (add Basis07.row653 node01078))) (add (add (add (t Basis07.row655) Basis07.row658) (add node04422 node00433)) (add (add Basis07.row664 node02456) (add (t Basis07.row668) Basis07.row670))))))) (add (add (add (add (add (add (t Basis07.row670) (add node00113 node01920)) (add (add node04466 (t Basis07.row680)) (add (t Basis07.row681) Basis07.row684))) (add (add (add (t Basis07.row685) node00734) (add (t Basis07.row688) Basis07.row689)) (add (add (t Basis07.row689) (t Basis07.row690)) (add Basis07.row692 node04385)))) (add (add (add (add (t Basis07.row695) Basis07.row697) (add node01085 node01726)) (add (add node00555 node00324) (add node02199 (t Basis07.row707)))) (add (add (add node03799 Basis07.row713) (add node02174 node00578)) (add (add Basis07.row719 node00386) (add node00801 node01141))))) (add (add (add (add node00325 (add Basis07.row731 (t Basis07.row733))) (add (add node02076 (t Basis07.row736)) (add Basis07.row737 node00557))) (add (add (add node01331 (t Basis07.row745)) (add (t Basis07.row748) (t Basis07.row749))) (add (add node01905 (t Basis07.row752)) (add (t Basis07.row753) node04025)))) (add (add (add (add node02511 Basis07.row761) (add (t Basis07.row762) Basis07.row764)) (add (add Basis07.row766 Basis07.row767) (add node02457 node02891))) (add (add (add Basis07.row774 node01202) (add node02723 node02610)) (add (add Basis07.row780 (t Basis07.row781)) (add Basis07.row783 Basis07.row784)))))) (add (add (add (add (add (t Basis07.row785) (add (t Basis07.row786) (t Basis07.row787))) (add (add node01670 Basis07.row790) (add node00188 node00903))) (add (add (add node03401 node00280) (add node02268 node03321)) (add (add node01400 node01979) (add node00986 Basis07.row815)))) (add (add (add (add Basis07.row816 (t Basis07.row816)) (add (t Basis07.row818) Basis07.row819)) (add (add Basis07.row820 node00202) (add node00079 node00837))) (add (add (add Basis07.row828 Basis07.row830) (add (t Basis07.row830) node03812)) (add (add node01019 Basis07.row838) (add Basis07.row839 Basis07.row840))))) (add (add (add (add (add (t Basis07.row842) Basis07.row844) (add node02214 node02203)) (add (add (t Basis07.row851) Basis07.row852) (add node03406 Basis07.row857))) (add (add (add (t Basis07.row858) Basis07.row859) (add node02019 node00876)) (add (add node01119 node00203) (add node01500 Basis07.row869)))) (add (add (add (add node00204 (t Basis07.row872)) (add node02460 Basis07.row877)) (add (add Basis07.row881 Basis07.row882) (add (t Basis07.row883) Basis07.row884))) (add (add (add Basis07.row886 (t Basis07.row886)) (add node01249 node02253)) (add (add Basis07.row892 Basis07.row893) (add (t Basis07.row894) Basis07.row895)))))))))

private theorem row192 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 192 (0, 0)) ((rowsAt 10).getD 192 (0, 0)) := by
  apply of_certificate witness192
  · decide +kernel
  · decide +kernel

private noncomputable def witness193 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row053

private theorem row193 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 193 (0, 0)) ((rowsAt 10).getD 193 (0, 0)) := by
  apply of_certificate witness193
  · decide +kernel
  · decide +kernel

private noncomputable def witness194 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add node03048 (add (t Basis07.row002) node00080)) (add (add (t Basis07.row005) (t Basis07.row006)) (add Basis07.row007 Basis07.row008))) (add (add (add (t Basis07.row008) node01886) (add node00591 node00990)) (add (add node00190 node01273) (add Basis07.row021 node00918)))) (add (add (add (add node00559 (t Basis07.row027)) (add node02175 Basis07.row032)) (add (add Basis07.row033 node01408) (add node00283 (t Basis07.row039)))) (add (add (add node01120 (t Basis07.row041)) (add node04097 Basis07.row048)) (add (add node02211 node04203) (add node01817 node00838))))) (add (add (add (add (add (t Basis07.row057) (t Basis07.row058)) (add node03973 Basis07.row062)) (add (add node01703 node01375) (add node01856 node00106))) (add (add (add (t Basis07.row071) (t Basis07.row073)) (add Basis07.row074 Basis07.row075)) (add (add Basis07.row077 node01944) (add (t Basis07.row079) Basis07.row080)))) (add (add (add (add (t Basis07.row081) Basis07.row083) (add Basis07.row084 node03340)) (add (add Basis07.row088 node01945) (add (t Basis07.row091) (t Basis07.row092)))) (add (add (add node03099 Basis07.row097) (add node00360 Basis07.row100)) (add (add Basis07.row101 node02093) (add node00496 node02032)))))) (add (add (add (add (add Basis07.row107 (add node00477 node02094)) (add (add (t Basis07.row111) Basis07.row112) (add Basis07.row114 (t Basis07.row114)))) (add (add (add node01217 node03949) (add (t Basis07.row119) node00693)) (add (add node02973 (t Basis07.row124)) (add Basis07.row125 node01795)))) (add (add (add (add (t Basis07.row130) node04123) (add node03040 Basis07.row137)) (add (add node01948 (t Basis07.row141)) (add node01620 node00515))) (add (add (add node01552 (t Basis07.row149)) (add node02095 Basis07.row152)) (add (add Basis07.row153 (t Basis07.row154)) (add (t Basis07.row155) (t Basis07.row156)))))) (add (add (add (add (add Basis07.row157 (t Basis07.row158)) (add node00780 Basis07.row162)) (add (add node02859 (t Basis07.row166)) (add Basis07.row168 node03497))) (add (add (add node01649 Basis07.row175) (add node03414 Basis07.row178)) (add (add (t Basis07.row181) node02328) (add (t Basis07.row184) node01472)))) (add (add (add (add Basis07.row189 node03347) (add (t Basis07.row193) (t Basis07.row194))) (add (add (t Basis07.row195) Basis07.row196) (add Basis07.row197 Basis07.row199))) (add (add (add node02936 node03297) (add Basis07.row206 Basis07.row207)) (add (add node02794 node00394) (add node01349 Basis07.row215))))))) (add (add (add (add (add (add (t Basis07.row215) (add (t Basis07.row216) node02687)) (add (add node01388 (t Basis07.row223)) (add Basis07.row227 (t Basis07.row229)))) (add (add (add Basis07.row232 (t Basis07.row232)) (add Basis07.row233 Basis07.row234)) (add (add node02145 node02869) (add node01583 node03736)))) (add (add (add (add Basis07.row243 node01502) (add node00011 node02609)) (add (add (t Basis07.row250) Basis07.row251) (add node00014 node00481))) (add (add (add (t Basis07.row257) node02559) (add (t Basis07.row260) node01892)) (add (add node00398 Basis07.row268) (add node00638 (t Basis07.row271)))))) (add (add (add (add (add node02320 node02264) (add node01558 Basis07.row282)) (add (add (t Basis07.row282) (t Basis07.row283)) (add node01037 (t Basis07.row287)))) (add (add (add (t Basis07.row288) Basis07.row290) (add node01467 (t Basis07.row293))) (add (add node02507 (t Basis07.row296)) (add node02907 (t Basis07.row301))))) (add (add (add (add node00792 node04090) (add node01769 Basis07.row310)) (add (add node01208 Basis07.row313) (add node04212 (t Basis07.row316)))) (add (add (add node01047 (t Basis07.row320)) (add (t Basis07.row322) node03759)) (add (add node00015 Basis07.row327) (add node02519 Basis07.row331)))))) (add (add (add (add (add (t Basis07.row331) (add node02230 (t Basis07.row334))) (add (add Basis07.row335 node03682) (add node02437 node02924))) (add (add (add node01520 node01309) (add node00784 node00598)) (add (add (t Basis07.row349) node03982) (add (t Basis07.row353) node01415)))) (add (add (add (add Basis07.row357 Basis07.row358) (add node01521 node03499)) (add (add node02908 node00845) (add (t Basis07.row368) Basis07.row369))) (add (add (add node00422 node02567) (add Basis07.row374 node01709)) (add (add node03201 node02560) (add node03632 node00809))))) (add (add (add (add (add Basis07.row389 (t Basis07.row389)) (add Basis07.row390 node01999)) (add (add node04134 (t Basis07.row396)) (add Basis07.row398 Basis07.row399))) (add (add (add (t Basis07.row399) node01711) (add Basis07.row402 Basis07.row403)) (add (add Basis07.row404 Basis07.row405) (add Basis07.row406 node00574)))) (add (add (add (add node01522 node02102) (add Basis07.row413 (t Basis07.row414))) (add (add (t Basis07.row415) node01832) (add node03505 node01833))) (add (add (add (t Basis07.row423) (t Basis07.row426)) (add (t Basis07.row427) Basis07.row428)) (add (add (t Basis07.row429) node01835) (add (t Basis07.row432) (t Basis07.row433))))))))) (add (add (add (add (add (add (add Basis07.row435 (add Basis07.row436 Basis07.row437)) (add (add (t Basis07.row438) Basis07.row441) (add node03722 Basis07.row445))) (add (add (add Basis07.row447 Basis07.row449) (add (t Basis07.row450) Basis07.row451)) (add (add node00931 node01351) (add Basis07.row456 Basis07.row458)))) (add (add (add (add (t Basis07.row459) Basis07.row460) (add Basis07.row461 Basis07.row462)) (add (add node03113 (t Basis07.row466)) (add node02804 node03484))) (add (add (add (t Basis07.row471) Basis07.row473) (add Basis07.row474 node01716)) (add (add Basis07.row480 node00791) (add node04282 (t Basis07.row485)))))) (add (add (add (add (add (t Basis07.row487) Basis07.row488) (add Basis07.row489 Basis07.row492)) (add (add (t Basis07.row493) node00318) (add node03825 node00642))) (add (add (add Basis07.row502 node02990) (add node00739 node00504)) (add (add node02450 Basis07.row513) (add Basis07.row514 node03384)))) (add (add (add (add Basis07.row520 node02155) (add (t Basis07.row523) (t Basis07.row524))) (add (add (t Basis07.row525) Basis07.row526) (add Basis07.row527 node00430))) (add (add (add node00156 node02397) (add node01355 node02191)) (add (add node02451 node01108) (add Basis07.row542 (t Basis07.row543))))))) (add (add (add (add (add Basis07.row544 (add (t Basis07.row545) node00319)) (add (add node02705 (t Basis07.row552)) (add node02058 node00111))) (add (add (add node02163 Basis07.row560) (add node03075 node01938)) (add (add node03329 Basis07.row569) (add (t Basis07.row571) node02398)))) (add (add (add (add Basis07.row576 node00070) (add Basis07.row579 (t Basis07.row579))) (add (add node03417 node04145) (add (t Basis07.row586) (t Basis07.row587)))) (add (add (add Basis07.row588 (t Basis07.row590)) (add (t Basis07.row592) Basis07.row593)) (add (add (t Basis07.row593) node03310) (add node00489 node02031))))) (add (add (add (add (add Basis07.row601 node01746) (add node00764 node00964)) (add (add Basis07.row609 (t Basis07.row609)) (add node02258 node00794))) (add (add (add node02562 (t Basis07.row616)) (add node02578 node00576)) (add (add Basis07.row622 node00716) (add node02629 Basis07.row626)))) (add (add (add (add node02237 Basis07.row630) (add node00567 node02238)) (add (add node03028 Basis07.row639) (add Basis07.row640 node00040))) (add (add (add node03145 node01032) (add node02300 node00923)) (add (add node00745 node04452) (add (t Basis07.row656) Basis07.row659))))))) (add (add (add (add (add (add Basis07.row660 (add (t Basis07.row661) Basis07.row663)) (add (add node02799 node03268) (add node04233 (t Basis07.row670)))) (add (add (add (t Basis07.row672) node01626) (add node03043 node03894)) (add (add node01496 node03119) (add node01461 node03459)))) (add (add (add (add node01724 node03542) (add node01634 (t Basis07.row698))) (add (add node02878 node00957) (add node02390 node01848))) (add (add (add Basis07.row706 node00529) (add (t Basis07.row708) Basis07.row713)) (add (add Basis07.row714 node01462) (add node00632 Basis07.row719))))) (add (add (add (add (add node02260 node02133) (add (t Basis07.row724) (t Basis07.row728))) (add (add node01612 (t Basis07.row731)) (add Basis07.row732 (t Basis07.row735)))) (add (add (add Basis07.row737 node02301) (add node00451 node01859)) (add (add node01331 (t Basis07.row746)) (add Basis07.row749 (t Basis07.row749))))) (add (add (add (add Basis07.row752 (t Basis07.row752)) (add node02218 node03930)) (add (add node00452 node00841) (add (t Basis07.row762) (t Basis07.row763)))) (add (add (add Basis07.row764 (t Basis07.row765)) (add (t Basis07.row769) Basis07.row770)) (add (add (t Basis07.row771) (t Basis07.row773)) (add Basis07.row775 Basis07.row776)))))) (add (add (add (add (add (add node00004 node01058) (add (t Basis07.row784) node02384)) (add (add node00390 Basis07.row789) (add (t Basis07.row790) Basis07.row791))) (add (add (add node01493 Basis07.row794) (add node02249 node03966)) (add (add node01989 node02016) (add Basis07.row807 node03334)))) (add (add (add (add (t Basis07.row811) (t Basis07.row812)) (add node00986 Basis07.row817)) (add (add (t Basis07.row817) node01081) (add node00919 node01793))) (add (add (add Basis07.row824 (t Basis07.row825)) (add node00685 (t Basis07.row828))) (add (add node02126 node03547) (add node03125 node03800))))) (add (add (add (add (add Basis07.row840 node00692) (add node00863 (t Basis07.row844))) (add (add (t Basis07.row845) node02947) (add node02203 node02018))) (add (add (add Basis07.row853 Basis07.row854) (add node03548 Basis07.row859)) (add (add node01786 node01227) (add node01020 (t Basis07.row866))))) (add (add (add (add (t Basis07.row869) node01532) (add (t Basis07.row872) node01918)) (add (add node03407 node01060) (add node00248 (t Basis07.row883)))) (add (add (add Basis07.row884 Basis07.row885) (add (t Basis07.row885) node01249)) (add (add (t Basis07.row888) node00146) (add (t Basis07.row893) (t Basis07.row894))))))))))

private theorem row194 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 194 (0, 0)) ((rowsAt 10).getD 194 (0, 0)) := by
  apply of_certificate witness194
  · decide +kernel
  · decide +kernel

private noncomputable def witness195 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add node03048 (add (t Basis07.row003) (t Basis07.row004))) (add (add node04039 (t Basis07.row009)) (add (t Basis07.row010) node01064))) (add (add (add node00990 (t Basis07.row015)) (add Basis07.row017 node01273)) (add (add Basis07.row021 node00634) (add (t Basis07.row024) (t Basis07.row025))))) (add (add (add node00866 (add node00712 node00179)) (add (add (t Basis07.row033) Basis07.row034) (add Basis07.row035 node01122))) (add (add (add node01497 node03827) (add node02309 node01475)) (add (add node00908 (t Basis07.row048)) (add node00475 node01644))))) (add (add (add (add node02666 (add node00072 Basis07.row058)) (add (add Basis07.row061 Basis07.row064) (add Basis07.row065 Basis07.row067))) (add (add (add node04328 Basis07.row072) (add Basis07.row073 (t Basis07.row074))) (add (add (t Basis07.row075) node03131) (add node03976 node00135)))) (add (add (add (add Basis07.row085 node01596) (add node00511 node01405)) (add (add node03753 node01986) (add node01631 node02841))) (add (add (add Basis07.row102 (t Basis07.row102)) (add node04037 Basis07.row109)) (add (add Basis07.row110 (t Basis07.row111)) (add (t Basis07.row113) (t Basis07.row114))))))) (add (add (add (add (add node00297 (add node01112 node00693)) (add (add node02732 Basis07.row126) (add (t Basis07.row126) Basis07.row128))) (add (add (add (t Basis07.row128) Basis07.row130) (add node04123 Basis07.row134)) (add (add (t Basis07.row135) node00909) (add node00497 node00028)))) (add (add (add (add (t Basis07.row140) (t Basis07.row141)) (add Basis07.row143 Basis07.row145)) (add (add (t Basis07.row145) node01821) (add node00287 node00561))) (add (add (add (t Basis07.row154) (t Basis07.row155)) (add node00299 node00439)) (add (add Basis07.row161 Basis07.row162) (add (t Basis07.row163) node04469))))) (add (add (add (add node01640 (add node03675 node03039)) (add (add Basis07.row175 node03961) (add (t Basis07.row178) node01823))) (add (add (add Basis07.row181 node01396) (add Basis07.row184 node02429)) (add (add node00766 node00162) (add node02354 node01765)))) (add (add (add (add node02734 Basis07.row199) (add (t Basis07.row199) Basis07.row202)) (add (add node03101 (t Basis07.row205)) (add (t Basis07.row207) Basis07.row211))) (add (add (add (t Basis07.row211) (t Basis07.row212)) (add (t Basis07.row214) node01453)) (add (add node03639 node04052) (add Basis07.row228 Basis07.row230))))))) (add (add (add (add (add (add Basis07.row231 (add Basis07.row232 Basis07.row234)) (add (add (t Basis07.row236) Basis07.row237) (add Basis07.row238 Basis07.row239))) (add (add (add node03044 node02484) (add (t Basis07.row247) (t Basis07.row248))) (add (add node01066 node01244) (add Basis07.row255 node02795)))) (add (add (add node02643 (add (t Basis07.row262) (t Basis07.row263))) (add (add (t Basis07.row264) node00398) (add node00254 Basis07.row272))) (add (add (add (t Basis07.row274) Basis07.row277) (add node02796 Basis07.row280)) (add (add Basis07.row281 node03300) (add (t Basis07.row285) Basis07.row286))))) (add (add (add (add node02625 (add (t Basis07.row290) (t Basis07.row291))) (add (add Basis07.row292 Basis07.row294) (add (t Basis07.row295) node04274))) (add (add (add node00953 node00695) (add node00792 node00502)) (add (add node01768 (t Basis07.row308)) (add node02626 node03057)))) (add (add (add (add (t Basis07.row316) (t Basis07.row319)) (add Basis07.row321 (t Basis07.row321))) (add (add (t Basis07.row324) (t Basis07.row325)) (add node03257 Basis07.row331))) (add (add (add (t Basis07.row332) Basis07.row334) (add node00980 node00995)) (add (add node00773 node00542) (add (t Basis07.row343) node01309)))))) (add (add (add (add (add (t Basis07.row346) (add node03424 node04306)) (add (add node00244 node01215) (add Basis07.row355 node00077))) (add (add (add (t Basis07.row359) Basis07.row360) (add (t Basis07.row360) node01214)) (add (add Basis07.row364 node00274) (add node00845 Basis07.row368)))) (add (add (add (add Basis07.row369 node01389) (add node03703 (t Basis07.row376))) (add (add Basis07.row378 (t Basis07.row379)) (add Basis07.row380 (t Basis07.row380)))) (add (add (add node01282 node02657) (add node00194 (t Basis07.row390))) (add (add node03134 node01126) (add node02263 Basis07.row398))))) (add (add (add (add Basis07.row399 (add (t Basis07.row399) Basis07.row400)) (add (add Basis07.row403 node02331) (add node00445 node02737))) (add (add (add node02490 Basis07.row411) (add Basis07.row412 Basis07.row413)) (add (add (t Basis07.row414) node01321) (add Basis07.row419 (t Basis07.row420))))) (add (add (add (add (t Basis07.row421) Basis07.row422) (add Basis07.row423 Basis07.row424)) (add (add node03158 node02707) (add node02332 (t Basis07.row431)))) (add (add (add node03078 node01030) (add node00586 node03659)) (add (add Basis07.row441 (t Basis07.row441)) (add node01399 (t Basis07.row447))))))))) (add (add (add (add (add (add (add Basis07.row448 (add (t Basis07.row448) node03346)) (add (add node00339 (t Basis07.row454)) (add Basis07.row457 node03468))) (add (add (add (t Basis07.row460) (t Basis07.row461)) (add Basis07.row463 node01092)) (add (add node01014 node00706) (add node01541 node00485)))) (add (add (add (t Basis07.row472) (add (t Basis07.row473) Basis07.row475)) (add (add (t Basis07.row475) (t Basis07.row476)) (add Basis07.row480 node02003))) (add (add (add Basis07.row484 node02189) (add (t Basis07.row487) node03451)) (add (add Basis07.row491 node00050) (add node00318 Basis07.row498))))) (add (add (add (add node00850 (add Basis07.row500 node01354)) (add (add Basis07.row504 (t Basis07.row505)) (add node01985 (t Basis07.row508)))) (add (add (add (t Basis07.row509) (t Basis07.row510)) (add (t Basis07.row511) node01469)) (add (add (t Basis07.row516) Basis07.row517) (add Basis07.row518 (t Basis07.row519))))) (add (add (add (add Basis07.row520 node01752) (add (t Basis07.row522) Basis07.row523)) (add (add (t Basis07.row525) Basis07.row527) (add (t Basis07.row527) Basis07.row529))) (add (add (add (t Basis07.row530) node03208) (add node00954 node02166)) (add (add (t Basis07.row537) node01722) (add node02913 (t Basis07.row543))))))) (add (add (add (add (add Basis07.row544 (add (t Basis07.row547) node02705)) (add (add node03924 node02058) (add Basis07.row557 (t Basis07.row558)))) (add (add (add node01961 Basis07.row563) (add (t Basis07.row563) node00228)) (add (add node03345 (t Basis07.row571)) (add Basis07.row573 Basis07.row574)))) (add (add (add (add (t Basis07.row574) (t Basis07.row576)) (add node00757 node02072)) (add (add Basis07.row583 (t Basis07.row584)) (add (t Basis07.row586) node02008))) (add (add (add Basis07.row589 node03456) (add (t Basis07.row592) node02363)) (add (add Basis07.row596 (t Basis07.row596)) (add node02059 node00322))))) (add (add (add (add node02298 (add Basis07.row606 node00779)) (add (add node01031 Basis07.row610) (add Basis07.row611 Basis07.row612))) (add (add (add node02863 Basis07.row617) (add node01245 node01055)) (add (add node03162 Basis07.row623) (add node02754 Basis07.row627)))) (add (add (add (add Basis07.row628 (t Basis07.row630)) (add node02238 node03028)) (add (add (t Basis07.row637) Basis07.row639) (add node00854 Basis07.row644))) (add (add (add node01040 node02300) (add node00277 node02061)) (add (add node03654 Basis07.row657) (add Basis07.row658 node00168))))))) (add (add (add (add (add (add (t Basis07.row660) (add Basis07.row662 (t Basis07.row662))) (add (add node02769 node01161) (add Basis07.row668 node02497))) (add (add (add node00246 Basis07.row676) (add node00213 (t Basis07.row680))) (add (add Basis07.row683 node03394) (add node01287 node03395)))) (add (add (add node00008 (add (t Basis07.row691) node02823)) (add (add node01229 node00186) (add (t Basis07.row701) (t Basis07.row702)))) (add (add (add Basis07.row704 (t Basis07.row707)) (add Basis07.row710 node02647)) (add (add node00187 Basis07.row716) (add (t Basis07.row718) (t Basis07.row719)))))) (add (add (add (add Basis07.row720 (add Basis07.row721 (t Basis07.row721))) (add (add node01903 (t Basis07.row724)) (add Basis07.row726 node02542))) (add (add (add (t Basis07.row729) node04485) (add node00887 node01380)) (add (add node03929 Basis07.row742) (add node04481 node02305)))) (add (add (add (add node00296 Basis07.row752) (add Basis07.row753 (t Basis07.row754))) (add (add node00788 node00352) (add node00452 node04081))) (add (add (add (t Basis07.row764) node02421) (add node00387 (t Basis07.row769))) (add (add Basis07.row771 node01142) (add (t Basis07.row774) Basis07.row776)))))) (add (add (add (add (add node00004 (add node02014 node02023)) (add (add node02270 Basis07.row788) (add (t Basis07.row791) node02458))) (add (add (add (t Basis07.row794) Basis07.row795) (add node01614 node01729)) (add (add (t Basis07.row803) Basis07.row805) (add (t Basis07.row806) Basis07.row807)))) (add (add (add (add node04166 node01352) (add node00878 (t Basis07.row816))) (add (add (t Basis07.row817) node00659) (add Basis07.row820 node01793))) (add (add (add (t Basis07.row824) node02388) (add node02126 node04324)) (add (add node00880 node03994) (add (t Basis07.row839) node00590))))) (add (add (add (add node00043 (add Basis07.row845 (t Basis07.row845))) (add (add (t Basis07.row847) (t Basis07.row849)) (add (t Basis07.row850) (t Basis07.row851)))) (add (add (add (t Basis07.row852) node03406) (add node02996 (t Basis07.row859))) (add (add node02019 node03339) (add (t Basis07.row865) node04435)))) (add (add (add (add Basis07.row870 Basis07.row871) (add node02389 (t Basis07.row874))) (add (add (t Basis07.row875) node03819) (add (t Basis07.row879) (t Basis07.row881)))) (add (add (add node00877 node01130) (add node00719 node01082)) (add (add node00235 node00668) (add node01303 Basis07.row895)))))))))

private theorem row195 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 195 (0, 0)) ((rowsAt 10).getD 195 (0, 0)) := by
  apply of_certificate witness195
  · decide +kernel
  · decide +kernel

private noncomputable def witness196 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row054

private theorem row196 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 196 (0, 0)) ((rowsAt 10).getD 196 (0, 0)) := by
  apply of_certificate witness196
  · decide +kernel
  · decide +kernel

private noncomputable def witness197 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add node04354 (add Basis07.row003 node02506)) (add (add Basis07.row009 node03082) (add Basis07.row012 (t Basis07.row012)))) (add (add (add (t Basis07.row013) node01741) (add node01941 node03289)) (add (add node00702 node02887) (add Basis07.row025 Basis07.row026)))) (add (add (add Basis07.row027 (add Basis07.row028 (t Basis07.row028))) (add (add Basis07.row029 node01448) (add Basis07.row034 node03413))) (add (add (add node00220 (t Basis07.row042)) (add node00436 (t Basis07.row046))) (add (add Basis07.row047 Basis07.row048) (add node02665 node01758))))) (add (add (add (add node03510 (add (t Basis07.row057) (t Basis07.row058))) (add (add node01536 node00268) (add node04088 Basis07.row066))) (add (add (add node00661 (t Basis07.row069)) (add (t Basis07.row070) Basis07.row071)) (add (add Basis07.row073 (t Basis07.row073)) (add node01327 node02954)))) (add (add (add (t Basis07.row079) (add node01595 node00308)) (add (add node03340 node02813) (add node03965 Basis07.row094))) (add (add (add (t Basis07.row094) node00009) (add node01361 node00074)) (add (add node01946 node00753) (add node02689 (t Basis07.row107))))))) (add (add (add (add (add (t Basis07.row108) (add node00147 Basis07.row111)) (add (add node01022 (t Basis07.row114)) (add node01217 node01112))) (add (add (add node02317 node02732) (add node01124 (t Basis07.row125))) (add (add (t Basis07.row126) node02714) (add (t Basis07.row130) node03717)))) (add (add (add Basis07.row134 (add node04450 node02639)) (add (add node02226 (t Basis07.row144)) (add node01546 node00379))) (add (add (add node00881 (t Basis07.row153)) (add Basis07.row158 node01145)) (add (add node00780 (t Basis07.row162)) (add node00180 node02370))))) (add (add (add (add node02851 (add node01409 node00584)) (add (add (t Basis07.row180) (t Basis07.row181)) (add (t Basis07.row182) node01362))) (add (add (add node03344 Basis07.row194) (add node02530 node02432)) (add (add node00251 node01044) (add node03101 node00252)))) (add (add (add (add Basis07.row208 node01633) (add (t Basis07.row210) node01349)) (add (add (t Basis07.row216) Basis07.row217) (add (t Basis07.row217) (t Basis07.row219)))) (add (add (add node00774 (t Basis07.row223)) (add Basis07.row225 (t Basis07.row226))) (add (add Basis07.row228 (t Basis07.row228)) (add node02430 node03837))))))) (add (add (add (add (add (add Basis07.row236 (add node00678 (t Basis07.row239))) (add (add Basis07.row240 node01089) (add node00978 (t Basis07.row244)))) (add (add (add (t Basis07.row246) Basis07.row247) (add Basis07.row248 Basis07.row250)) (add (add (t Basis07.row250) Basis07.row252) (add (t Basis07.row254) (t Basis07.row255))))) (add (add (add Basis07.row256 (add node03197 node01101)) (add (add (t Basis07.row260) (t Basis07.row262)) (add node01892 (t Basis07.row265)))) (add (add (add Basis07.row267 (t Basis07.row267)) (add (t Basis07.row269) node03428)) (add (add node00272 (t Basis07.row276)) (add node00206 node00596))))) (add (add (add (add (t Basis07.row286) (add (t Basis07.row287) (t Basis07.row288))) (add (add (t Basis07.row289) (t Basis07.row290)) (add node01559 node01046))) (add (add (add node00021 (t Basis07.row296)) (add node03746 node00695)) (add (add node03839 (t Basis07.row308)) (add (t Basis07.row309) (t Basis07.row311))))) (add (add (add (add node04212 (t Basis07.row316)) (add Basis07.row322 node02773)) (add (add (t Basis07.row327) node00460) (add node03918 (t Basis07.row333)))) (add (add (add (t Basis07.row334) Basis07.row336) (add node00995 (t Basis07.row340))) (add (add (t Basis07.row341) (t Basis07.row342)) (add (t Basis07.row343) node02053)))))) (add (add (add (add (add (t Basis07.row346) (add node01829 (t Basis07.row350))) (add (add node00244 (t Basis07.row354)) (add (t Basis07.row355) Basis07.row356))) (add (add (add node00563 node03348) (add node01029 Basis07.row365)) (add (add Basis07.row366 node04406) (add (t Basis07.row370) (t Basis07.row371))))) (add (add (add (t Basis07.row372) (add Basis07.row373 Basis07.row374)) (add (add Basis07.row376 node01083) (add Basis07.row379 Basis07.row380))) (add (add (add (t Basis07.row380) node02560) (add node00809 (t Basis07.row387))) (add (add node03719 node01481) (add node02376 node02986))))) (add (add (add (add node00019 (add Basis07.row401 (t Basis07.row402))) (add (add node02331 node01656) (add Basis07.row409 Basis07.row411))) (add (add (add Basis07.row412 node02566) (add node03157 (t Basis07.row417))) (add (add node03505 node01510) (add node03597 (t Basis07.row425))))) (add (add (add (add node00522 Basis07.row429) (add Basis07.row430 node02658)) (add (add Basis07.row435 Basis07.row436) (add node01073 node04375))) (add (add (add node00427 node03379) (add Basis07.row446 Basis07.row447)) (add (add Basis07.row450 Basis07.row451) (add (t Basis07.row452) Basis07.row455)))))))) (add (add (add (add (add (add (add Basis07.row457 (add node01564 (t Basis07.row460))) (add (add Basis07.row461 node03085) (add (t Basis07.row466) node02473))) (add (add (add node01093 node01209) (add node01440 node00575)) (add (add node00341 node00154) (add Basis07.row484 Basis07.row485)))) (add (add (add (t Basis07.row486) (add node01051 node01069)) (add (add (t Basis07.row491) Basis07.row493) (add node00587 node02292))) (add (add (add node00850 (t Basis07.row501)) (add node00370 node02711)) (add (add (t Basis07.row505) Basis07.row506) (add (t Basis07.row508) (t Basis07.row510)))))) (add (add (add (add (t Basis07.row511) (add node02700 (t Basis07.row515))) (add (add Basis07.row516 (t Basis07.row518)) (add (t Basis07.row520) (t Basis07.row521)))) (add (add (add (t Basis07.row525) (t Basis07.row526)) (add node00261 node01281)) (add (add node00086 node00954) (add Basis07.row536 (t Basis07.row537))))) (add (add (add node04117 (add (t Basis07.row541) node01547)) (add (add Basis07.row545 node03728) (add node00165 node00449))) (add (add (add node00450 node01077) (add node02163 (t Basis07.row560))) (add (add (t Basis07.row561) node02730) (add node00732 node01381)))))) (add (add (add (add (add Basis07.row568 (add node00196 node01775)) (add (add Basis07.row573 (t Basis07.row573)) (add node00742 node02039))) (add (add (add node00101 (t Basis07.row580)) (add (t Basis07.row581) (t Basis07.row582))) (add (add Basis07.row584 (t Basis07.row584)) (add (t Basis07.row585) node00024)))) (add (add (add node00032 (add node04225 (t Basis07.row594))) (add (add Basis07.row596 Basis07.row598) (add (t Basis07.row598) Basis07.row600))) (add (add (add node01189 Basis07.row604) (add node02403 node00964)) (add (add Basis07.row609 Basis07.row612) (add (t Basis07.row612) node03989))))) (add (add (add (add Basis07.row617 (add Basis07.row618 node00999)) (add (add node03097 node02551) (add node03188 node01466))) (add (add (add Basis07.row630 node00198) (add (t Basis07.row633) node01179)) (add (add node00051 Basis07.row637) (add Basis07.row638 node02299)))) (add (add (add (add node02195 node00345) (add Basis07.row646 (t Basis07.row646))) (add (add node01691 node00923) (add node04104 Basis07.row657))) (add (add (add Basis07.row658 node01243) (add Basis07.row661 (t Basis07.row662))) (add (add node00924 (t Basis07.row668)) (add (t Basis07.row669) node00836))))))) (add (add (add (add (add (add node02337 (add (t Basis07.row674) Basis07.row675)) (add (add node00886 node01079) (add Basis07.row679 Basis07.row681))) (add (add (add node01847 node03895) (add node01461 Basis07.row688)) (add (add (t Basis07.row689) node00214) (add (t Basis07.row692) (t Basis07.row694))))) (add (add (add (t Basis07.row698) (add node03435 node01966)) (add (add Basis07.row705 (t Basis07.row709)) (add node00717 node02011))) (add (add (add node00707 (t Basis07.row717)) (add (t Basis07.row718) (t Basis07.row719))) (add (add Basis07.row720 node00351) (add Basis07.row723 Basis07.row724))))) (add (add (add (add (t Basis07.row724) (add Basis07.row727 Basis07.row728)) (add (add Basis07.row729 node02776) (add node03817 Basis07.row734))) (add (add (add Basis07.row735 (t Basis07.row736)) (add Basis07.row737 node01322)) (add (add (t Basis07.row739) Basis07.row741) (add Basis07.row744 node00217)))) (add (add (add (add node00003 node00263) (add node01861 (t Basis07.row753))) (add (add (t Basis07.row756) (t Basis07.row757)) (add node00452 node01180))) (add (add (add node00062 node00603) (add node00758 node02077)) (add (add node00531 node00353) (add (t Basis07.row776) node03731)))))) (add (add (add (add (add Basis07.row780 (add node00493 node01912)) (add (add (t Basis07.row786) (t Basis07.row787)) (add node01908 (t Basis07.row790)))) (add (add (add node03637 node01614) (add node02259 node00410)) (add (add node02268 node03712) (add node00454 node00329)))) (add (add (add node00218 (add Basis07.row816 Basis07.row817)) (add (add node01081 node00919) (add (t Basis07.row822) node03464))) (add (add (add node03190 Basis07.row831) (add Basis07.row832 node01910)) (add (add node00131 node00354) (add node00940 node01337))))) (add (add (add (add node00043 (add Basis07.row845 (t Basis07.row845))) (add (add node02947 Basis07.row850) (add node00752 node00966))) (add (add (add node00624 node00473) (add Basis07.row860 Basis07.row863)) (add (add (t Basis07.row863) (t Basis07.row867)) (add (t Basis07.row868) node00569)))) (add (add (add (add Basis07.row871 node01007) (add node00724 node00331)) (add (add node03467 Basis07.row880) (add node02611 (t Basis07.row883)))) (add (add (add Basis07.row884 node02885) (add node01249 node01193)) (add (add (t Basis07.row890) node02692) (add (t Basis07.row894) Basis07.row895)))))))))

private theorem row197 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 197 (0, 0)) ((rowsAt 10).getD 197 (0, 0)) := by
  apply of_certificate witness197
  · decide +kernel
  · decide +kernel

private noncomputable def witness198 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add Basis07.row001 (add Basis07.row002 node01376)) (add (add node01939 (t Basis07.row010)) (add Basis07.row012 Basis07.row013))) (add (add (add Basis07.row014 (t Basis07.row014)) (add node02931 Basis07.row018)) (add (add node02256 node00702) (add node00634 node04462)))) (add (add (add (add Basis07.row027 node00712) (add Basis07.row032 node01976)) (add (add node01122 node01497) (add Basis07.row041 node01450))) (add (add (add node03363 node01982) (add (t Basis07.row051) node01747)) (add (add Basis07.row054 (t Basis07.row056)) (add node00359 node02402))))) (add (add (add (add node00073 (add (t Basis07.row067) (t Basis07.row069))) (add (add node00916 (t Basis07.row071)) (add node03240 node01008))) (add (add (add Basis07.row078 node03294) (add Basis07.row081 node00308)) (add (add (t Basis07.row085) Basis07.row087) (add (t Basis07.row087) (t Basis07.row088))))) (add (add (add (add node02556 node04370) (add node02144 node00378)) (add (add node01676 node00636) (add Basis07.row104 Basis07.row106))) (add (add (add node01162 Basis07.row108) (add Basis07.row109 node02771)) (add (add (t Basis07.row112) node00362) (add node03557 (t Basis07.row117))))))) (add (add (add (add (add (t Basis07.row118) (add (t Basis07.row120) (t Basis07.row121))) (add (add Basis07.row125 node01880) (add (t Basis07.row128) Basis07.row130))) (add (add (add (t Basis07.row132) Basis07.row134) (add (t Basis07.row134) Basis07.row136)) (add (add Basis07.row138 node00479) (add node01514 Basis07.row144)))) (add (add (add (add node00515 (t Basis07.row146)) (add (t Basis07.row147) (t Basis07.row148))) (add (add Basis07.row151 node02393) (add node01515 node00768))) (add (add (add node01171 Basis07.row159) (add node02975 node00537)) (add (add node02739 (t Basis07.row166)) (add Basis07.row168 node04206))))) (add (add (add (add node01409 (add (t Basis07.row173) (t Basis07.row174))) (add (add (t Basis07.row175) Basis07.row176) (add node02706 (t Basis07.row179)))) (add (add (add (t Basis07.row180) node00181) (add node01362 (t Basis07.row187))) (add (add node01320 node02209) (add node01765 node02432)))) (add (add (add (add (t Basis07.row199) node00855) (add (t Basis07.row203) Basis07.row205)) (add (add node01291 (t Basis07.row208)) (add node02048 Basis07.row212))) (add (add (add node03664 Basis07.row217) (add (t Basis07.row217) (t Basis07.row218))) (add (add Basis07.row221 node00704) (add node00094 node03328))))))) (add (add (add (add (add (add (t Basis07.row227) (add Basis07.row230 Basis07.row231)) (add (add (t Basis07.row231) node00289) (add node02027 Basis07.row237))) (add (add (add Basis07.row238 Basis07.row239) (add node03736 Basis07.row243)) (add (add node00396 node04244) (add (t Basis07.row251) node02747)))) (add (add (add (add Basis07.row255 Basis07.row257) (add node00812 Basis07.row260)) (add (add Basis07.row261 node01518) (add node01557 (t Basis07.row265)))) (add (add (add node00994 node01436) (add node03428 node04209)) (add (add node03747 node01558) (add node00206 Basis07.row283))))) (add (add (add (add node00596 (add (t Basis07.row284) Basis07.row286)) (add (add Basis07.row287 (t Basis07.row290)) (add node00149 node00921))) (add (add (add node00628 Basis07.row297) (add node00459 Basis07.row299)) (add (add Basis07.row301 (t Basis07.row301)) (add node03519 Basis07.row305)))) (add (add (add (add Basis07.row307 (t Basis07.row308)) (add (t Basis07.row309) (t Basis07.row310))) (add (add (t Basis07.row311) Basis07.row313) (add (t Basis07.row313) (t Basis07.row314)))) (add (add (add node03679 Basis07.row318) (add (t Basis07.row318) Basis07.row319)) (add (add (t Basis07.row320) (t Basis07.row321)) (add Basis07.row323 Basis07.row326)))))) (add (add (add (add (add (t Basis07.row326) (add node01401 node04269)) (add (add node01333 node00995) (add node01827 node00573))) (add (add (add (t Basis07.row342) (t Basis07.row343)) (add node00082 Basis07.row346)) (add (add node00598 node00762) (add node00109 node00244)))) (add (add (add (add node00059 (t Basis07.row355)) (add node01267 node02330)) (add (add Basis07.row362 (t Basis07.row363)) (add (t Basis07.row364) Basis07.row365))) (add (add (add (t Basis07.row365) Basis07.row367) (add node01998 (t Basis07.row370))) (add (add (t Basis07.row371) (t Basis07.row372)) (add (t Basis07.row373) Basis07.row374))))) (add (add (add (add (t Basis07.row375) (add (t Basis07.row376) Basis07.row378)) (add (add node04451 node00336) (add node02448 Basis07.row386))) (add (add (add node02151 (t Basis07.row388)) (add node01049 node01277)) (add (add node00629 node01126) (add node03805 node03843)))) (add (add (add (add node02131 node00445) (add node02360 node00751)) (add (add node01563 node00564) (add Basis07.row415 (t Basis07.row415)))) (add (add (add Basis07.row417 node00257) (add node01605 Basis07.row423)) (add (add node03091 (t Basis07.row427)) (add Basis07.row428 node00613)))))))) (add (add (add (add (add (add (add (t Basis07.row432) (add (t Basis07.row433) Basis07.row434)) (add (add Basis07.row437 Basis07.row439) (add (t Basis07.row439) node02233))) (add (add (add node03380 (t Basis07.row445)) (add Basis07.row447 node03563)) (add (add Basis07.row455 node00260) (add Basis07.row458 (t Basis07.row459))))) (add (add (add (add node01837 node02134) (add node03113 node00706)) (add (add node01541 (t Basis07.row470)) (add Basis07.row473 Basis07.row476))) (add (add (add Basis07.row477 (t Basis07.row477)) (add node02002 Basis07.row482)) (add (add node02939 Basis07.row485) (add node02189 Basis07.row488))))) (add (add (add (add Basis07.row489 (add node00885 node03685)) (add (add node01660 node00487) (add node02415 node02030))) (add (add (add (t Basis07.row503) node00382) (add node01985 node03801)) (add (add Basis07.row512 node01917) (add (t Basis07.row516) node00799)))) (add (add (add (add node01072 node00554) (add node00643 node04240)) (add (add Basis07.row530 node00086) (add (t Basis07.row533) Basis07.row534))) (add (add (add (t Basis07.row534) node01663) (add node00544 node01036)) (add (add node01063 node02601) (add node03012 node02057)))))) (add (add (add (add (add node02627 (add node00911 node01289)) (add (add node02163 node04263) (add Basis07.row563 Basis07.row564))) (add (add (add (t Basis07.row565) node03306) (add Basis07.row569 node02496)) (add (add (t Basis07.row573) node04015) (add Basis07.row577 Basis07.row579)))) (add (add (add (add Basis07.row581 Basis07.row582) (add Basis07.row583 (t Basis07.row583))) (add (add node03536 node00024) (add node03489 node02363))) (add (add (add node03310 node00489) (add node01330 node00935)) (add (add (t Basis07.row602) (t Basis07.row603)) (add node02403 Basis07.row608))))) (add (add (add (add Basis07.row609 (add (t Basis07.row609) (t Basis07.row611))) (add (add node03988 Basis07.row617) (add node00667 node00830))) (add (add (add (t Basis07.row624) node02992) (add node01191 (t Basis07.row631))) (add (add (t Basis07.row632) Basis07.row633) (add node00469 node01526)))) (add (add (add (add node01723 Basis07.row642) (add (t Basis07.row643) Basis07.row645)) (add (add Basis07.row646 Basis07.row647) (add (t Basis07.row647) (t Basis07.row648)))) (add (add (add Basis07.row652 (t Basis07.row655)) (add Basis07.row658 node00346)) (add (add Basis07.row662 Basis07.row663) (add node01156 (t Basis07.row665)))))))) (add (add (add (add (add (add (t Basis07.row667) (add node01345 (t Basis07.row670))) (add (add node01270 Basis07.row674) (add Basis07.row675 node00185))) (add (add (add node01079 node02943) (add (t Basis07.row682) node03393)) (add (add node02140 Basis07.row688) (add Basis07.row691 node01724)))) (add (add (add (add node04031 Basis07.row697) (add node03716 node00957)) (add (add node01498 node00324) (add Basis07.row706 Basis07.row707))) (add (add (add node04252 node00293) (add Basis07.row714 node02174)) (add (add (t Basis07.row717) Basis07.row719) (add node01299 node01402))))) (add (add (add (add node01041 (add node01035 node02075)) (add (add Basis07.row730 (t Basis07.row730)) (add (t Basis07.row731) Basis07.row732))) (add (add (add Basis07.row733 node04378) (add Basis07.row737 Basis07.row740)) (add (add node01622 node00294) (add node00756 node01495)))) (add (add (add (add (t Basis07.row749) node01790) (add Basis07.row753 (t Basis07.row753))) (add (add node00988 (t Basis07.row758)) (add node00841 (t Basis07.row761)))) (add (add (add node01680 Basis07.row767) (add Basis07.row768 node01573)) (add (add Basis07.row773 Basis07.row774) (add (t Basis07.row774) (t Basis07.row776))))))) (add (add (add (add (add node00785 (add node00711 node00985)) (add (add node00103 Basis07.row785) (add Basis07.row786 node00390))) (add (add (add (t Basis07.row789) Basis07.row790) (add node01678 node03637)) (add (add node02526 (t Basis07.row798)) (add node02259 node00410)))) (add (add (add (add node02396 Basis07.row806) (add node01001 (t Basis07.row812))) (add (add (t Basis07.row814) node01808) (add (t Basis07.row819) Basis07.row821))) (add (add (add node02252 (t Basis07.row825)) (add node01809 Basis07.row831)) (add (add (t Basis07.row832) node01910) (add (t Basis07.row836) Basis07.row837))))) (add (add (add (add node04237 (add Basis07.row842 node00863)) (add (add node02261 Basis07.row847) (add (t Basis07.row848) node01981))) (add (add (add Basis07.row851 node01792) (add (t Basis07.row854) node02864)) (add (add (t Basis07.row858) node01301) (add node03339 node04433)))) (add (add (add (add node00145 node01796) (add (t Basis07.row869) node03996)) (add (add Basis07.row874 node03285) (add node02595 Basis07.row881))) (add (add (add Basis07.row882 node03090) (add node00959 Basis07.row887)) (add (add node02272 node02423) (add Basis07.row893 node00647)))))))))

private theorem row198 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 198 (0, 0)) ((rowsAt 10).getD 198 (0, 0)) := by
  apply of_certificate witness198
  · decide +kernel
  · decide +kernel

private noncomputable def witness199 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row055

private theorem row199 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 199 (0, 0)) ((rowsAt 10).getD 199 (0, 0)) := by
  apply of_certificate witness199
  · decide +kernel
  · decide +kernel

private noncomputable def witness200 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add (t Basis07.row001) (add (t Basis07.row002) (t Basis07.row003))) (add (add (t Basis07.row004) node03050) (add Basis07.row009 (t Basis07.row009)))) (add (add (add node01886 node00591) (add (t Basis07.row014) node01741)) (add (add node01941 Basis07.row021) (add node02702 node02091)))) (add (add (add (t Basis07.row027) (add (t Basis07.row030) (t Basis07.row033))) (add (add node01976 node02953) (add (t Basis07.row040) node01324))) (add (add (add node00436 node00857) (add node01549 (t Basis07.row050))) (add (add node03439 (t Basis07.row054)) (add node02848 node01701))))) (add (add (add (add (t Basis07.row059) (add node03974 node00268)) (add (add node02325 (t Basis07.row067)) (add node02740 Basis07.row071))) (add (add (add Basis07.row073 (t Basis07.row073)) (add Basis07.row075 node00191)) (add (add Basis07.row080 node02722) (add node03137 (t Basis07.row088))))) (add (add (add (add node01086 Basis07.row091) (add node03080 node02182)) (add (add node02478 node01818) (add node01760 (t Basis07.row104)))) (add (add (add node01819 (t Basis07.row110)) (add node03635 Basis07.row113)) (add (add node02582 node03195) (add node03622 Basis07.row121)))))) (add (add (add (add (add node02667 (add node00437 node01795)) (add (add (t Basis07.row128) node01947) (add Basis07.row133 node01005))) (add (add (add Basis07.row135 (t Basis07.row136)) (add (t Basis07.row137) node01317)) (add (add Basis07.row142 node02479) (add (t Basis07.row144) Basis07.row147)))) (add (add (add (add Basis07.row148 (t Basis07.row148)) (add Basis07.row149 node02095)) (add (add (t Basis07.row153) node01515) (add (t Basis07.row157) Basis07.row159))) (add (add (add (t Basis07.row159) (t Basis07.row160)) (add Basis07.row161 node01165)) (add (add (t Basis07.row164) node01226) (add (t Basis07.row168) node02969))))) (add (add (add (add node02045 (add node02515 (t Basis07.row175))) (add (add Basis07.row177 node00056) (add node01763 node02328))) (add (add (add node00594 node00498) (add node00766 node02021)) (add (add (t Basis07.row190) Basis07.row191) (add Basis07.row192 node01587)))) (add (add (add (add (t Basis07.row195) (t Basis07.row196)) (add (t Basis07.row197) Basis07.row198)) (add (add Basis07.row199 (t Basis07.row199)) (add node02936 node00300))) (add (add (add node00192 node02461) (add Basis07.row208 node01410)) (add (add Basis07.row211 node01621) (add Basis07.row214 (t Basis07.row216)))))))) (add (add (add (add (add (add node03434 (add (t Basis07.row219) node00774)) (add (add node02641 node00804) (add Basis07.row226 (t Basis07.row227)))) (add (add (add node01261 node03442) (add node02145 node02642)) (add (add node00095 Basis07.row241) (add (t Basis07.row242) node01623)))) (add (add (add (add (t Basis07.row246) node02609) (add Basis07.row250 (t Basis07.row251))) (add (add (t Basis07.row252) Basis07.row253) (add Basis07.row255 node03197))) (add (add (add node02643 node00761) (add Basis07.row265 (t Basis07.row266))) (add (add node00993 (t Basis07.row268)) (add node00058 node00519))))) (add (add (add (add Basis07.row274 (add Basis07.row276 Basis07.row277)) (add (add (t Basis07.row277) Basis07.row278) (add node00206 node03500))) (add (add (add (t Basis07.row284) Basis07.row286) (add (t Basis07.row287) (t Basis07.row288))) (add (add node01972 Basis07.row291) (add node00664 node01592)))) (add (add (add (add node03056 (t Basis07.row300)) (add (t Basis07.row301) node03487)) (add (add node03916 Basis07.row310) (add node01091 node00808))) (add (add (add (t Basis07.row317) Basis07.row319) (add node03759 Basis07.row326)) (add (add (t Basis07.row328) (t Basis07.row329)) (add node01125 node00686)))))) (add (add (add (add (add Basis07.row334 (add node03469 Basis07.row337)) (add (add Basis07.row338 (t Basis07.row340)) (add (t Basis07.row341) (t Basis07.row342)))) (add (add (add Basis07.row345 Basis07.row346) (add Basis07.row348 node02287)) (add (add node00109 node00244) (add node01215 (t Basis07.row355))))) (add (add (add (add node02054 (t Basis07.row359)) (add node03173 (t Basis07.row362))) (add (add Basis07.row364 (t Basis07.row367)) (add node00482 node00422))) (add (add (add node02896 Basis07.row374) (add node00038 Basis07.row378)) (add (add (t Basis07.row379) node00097) (add Basis07.row382 (t Basis07.row383)))))) (add (add (add (add Basis07.row384 (add Basis07.row385 node00194)) (add (add (t Basis07.row387) (t Basis07.row388)) (add (t Basis07.row389) Basis07.row390))) (add (add (add node01277 (t Basis07.row393)) (add Basis07.row394 Basis07.row396)) (add (add (t Basis07.row396) node02152) (add Basis07.row400 node03236)))) (add (add (add (add Basis07.row404 node02962) (add node01417 node01377)) (add (add Basis07.row411 Basis07.row412) (add node01657 node02428))) (add (add (add node03020 (t Basis07.row422)) (add node03985 node00982)) (add (add node00522 Basis07.row429) (add Basis07.row430 node02658)))))))) (add (add (add (add (add (add (add Basis07.row435 (add (t Basis07.row435) Basis07.row439)) (add (add Basis07.row440 node00697) (add node03380 (t Basis07.row445)))) (add (add (add (t Basis07.row446) (t Basis07.row447)) (add Basis07.row448 (t Basis07.row448))) (add (add (t Basis07.row449) Basis07.row451) (add Basis07.row452 Basis07.row454)))) (add (add (add (add node02492 node03112) (add (t Basis07.row460) Basis07.row461)) (add (add node00464 node03113) (add (t Basis07.row466) node02804))) (add (add (add node03653 node00368) (add node04359 (t Basis07.row477))) (add (add node00341 node02710) (add node01185 node04482))))) (add (add (add (add node01863 (add node00486 Basis07.row490)) (add (add node00824 (t Basis07.row492)) (add (t Basis07.row493) node02547))) (add (add (add node02292 Basis07.row499) (add (t Basis07.row499) node00642)) (add (add node00370 node02435) (add node00429 (t Basis07.row507))))) (add (add (add (add node01310 node04340) (add node02378 node01164)) (add (add (t Basis07.row517) Basis07.row519) (add node01752 node01523))) (add (add (add node00069 (t Basis07.row526)) (add Basis07.row529 Basis07.row530)) (add (add node01721 Basis07.row533) (add Basis07.row534 Basis07.row536)))))) (add (add (add (add (add node01232 (add (t Basis07.row540) (t Basis07.row541))) (add (add (t Basis07.row544) node00853) (add (t Basis07.row549) Basis07.row550))) (add (add (add Basis07.row551 (t Basis07.row552)) (add (t Basis07.row553) node01566)) (add (add node00933 Basis07.row559) (add Basis07.row560 node00002)))) (add (add (add (add node00432 node03224) (add Basis07.row570 node01486)) (add (add node00087 (t Basis07.row574)) (add node02652 Basis07.row579))) (add (add (add (t Basis07.row579) Basis07.row581) (add Basis07.row583 node00342)) (add (add Basis07.row586 node01428) (add node03343 Basis07.row592))))) (add (add (add (add node00829 (add node03161 node00527)) (add (add Basis07.row603 node01278) (add Basis07.row607 node00913))) (add (add (add node02691 (t Basis07.row617)) (add node00999 node00830)) (add (add node00007 Basis07.row625) (add Basis07.row626 node02206)))) (add (add (add (add (t Basis07.row629) Basis07.row631) (add Basis07.row632 node04146)) (add (add node00051 node01526) (add node00167 node01697))) (add (add (add (t Basis07.row643) node02240) (add node01040 node02132)) (add (add node00277 Basis07.row653) (add Basis07.row654 (t Basis07.row654)))))))) (add (add (add (add (add (add node03068 (add Basis07.row658 Basis07.row660)) (add (add (t Basis07.row661) node03266) (add Basis07.row665 node00506))) (add (add (add node03314 node01270) (add Basis07.row674 node03043)) (add (add node03476 node01900) (add (t Basis07.row683) Basis07.row685)))) (add (add (add (add node01287 node01129) (add (t Basis07.row690) node00292)) (add (add (t Basis07.row693) Basis07.row695) (add (t Basis07.row696) (t Basis07.row697)))) (add (add (add (t Basis07.row698) Basis07.row699) (add node00555 (t Basis07.row704))) (add (add node02198 Basis07.row708) (add (t Basis07.row708) node01438))))) (add (add (add (add (t Basis07.row713) (add (t Basis07.row715) Basis07.row716)) (add (add node01490 node01062) (add node02133 (t Basis07.row725)))) (add (add (add node02921 Basis07.row731) (add Basis07.row732 node00375)) (add (add node00887 node01322) (add node00451 (t Basis07.row745))))) (add (add (add (add node01781 node01332) (add node01905 node02218)) (add (add node03955 Basis07.row759) (add node04149 Basis07.row763))) (add (add (add Basis07.row764 (t Basis07.row766)) (add node02161 (t Basis07.row769))) (add (add (t Basis07.row772) node04107) (add (t Basis07.row777) (t Basis07.row778))))))) (add (add (add (add (add (t Basis07.row779) (add node04428 node01465)) (add (add node01424 node01506) (add node02015 (t Basis07.row792)))) (add (add (add Basis07.row793 node03565) (add node01404 node01170)) (add (add Basis07.row801 node02359) (add (t Basis07.row804) Basis07.row805)))) (add (add (add (add Basis07.row810 (t Basis07.row810)) (add node02308 Basis07.row813)) (add (add node02672 node00558) (add node03402 Basis07.row821))) (add (add (add Basis07.row822 Basis07.row823) (add (t Basis07.row823) node00837)) (add (add node00685 node04484) (add node02126 (t Basis07.row832)))))) (add (add (add (add (t Basis07.row834) (add node01019 node00354)) (add (add (t Basis07.row842) node00975) (add (t Basis07.row844) node00020))) (add (add (add node01981 node02018) (add (t Basis07.row854) (t Basis07.row855))) (add (add Basis07.row856 Basis07.row857) (add (t Basis07.row859) node03271)))) (add (add (add (add Basis07.row865 Basis07.row866) (add (t Basis07.row868) Basis07.row870)) (add (add Basis07.row872 node01290) (add node01187 (t Basis07.row879)))) (add (add (add node00105 node02611) (add node00455 Basis07.row886)) (add (add node03325 node00146) (add node00668 Basis07.row895)))))))))

private theorem row200 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 200 (0, 0)) ((rowsAt 10).getD 200 (0, 0)) := by
  apply of_certificate witness200
  · decide +kernel
  · decide +kernel

private noncomputable def witness201 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row477

private theorem row201 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 201 (0, 0)) ((rowsAt 10).getD 201 (0, 0)) := by
  apply of_certificate witness201
  · decide +kernel
  · decide +kernel

private noncomputable def witness202 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add node02930 (add node02506 Basis07.row008)) (add (add (t Basis07.row009) node01940) (add node00807 Basis07.row019))) (add (add (add (t Basis07.row019) node00842) (add node02782 Basis07.row025)) (add (add node00559 node00866) (add (t Basis07.row032) (t Basis07.row036))))) (add (add (add (add Basis07.row037 (t Basis07.row037)) (add Basis07.row040 node01450)) (add (add node00436 (t Basis07.row045)) (add node00626 Basis07.row049))) (add (add (add node00456 Basis07.row052) (add Basis07.row053 Basis07.row054)) (add (add (t Basis07.row056) node00267) (add Basis07.row060 node03974))))) (add (add (add (add node00391 (add Basis07.row065 Basis07.row066)) (add (add node00001 Basis07.row069) (add Basis07.row071 (t Basis07.row071)))) (add (add (add node03352 Basis07.row076) (add (t Basis07.row076) Basis07.row078)) (add (add Basis07.row079 node02477) (add (t Basis07.row083) node03250)))) (add (add (add (add (t Basis07.row087) node01945) (add node02225 node03080)) (add (add (t Basis07.row096) node00378) (add Basis07.row100 Basis07.row104))) (add (add (add Basis07.row105 Basis07.row106) (add node01162 node02407)) (add (add node02674 node04175) (add Basis07.row115 Basis07.row116)))))) (add (add (add (add (add Basis07.row117 (add node03622 (t Basis07.row121))) (add (add Basis07.row123 (t Basis07.row124)) (add Basis07.row125 (t Basis07.row125)))) (add (add (add node02043 node01023) (add node03295 node00238)) (add (add node01877 Basis07.row139) (add node02827 (t Basis07.row142))))) (add (add (add (add (t Basis07.row143) node02600) (add (t Basis07.row149) node02279)) (add (add (t Basis07.row152) Basis07.row153) (add Basis07.row154 (t Basis07.row155)))) (add (add (add (t Basis07.row156) (t Basis07.row157)) (add Basis07.row159 node03054)) (add (add node00537 node00950) (add Basis07.row165 (t Basis07.row165)))))) (add (add (add (add Basis07.row167 (add node00045 node02726)) (add (add node01468 node02516) (add node01763 (t Basis07.row182)))) (add (add (add (t Basis07.row183) (t Basis07.row184)) (add node02429 Basis07.row187)) (add (add node02067 (t Basis07.row190)) (add node00240 node00708)))) (add (add (add (add node02082 Basis07.row199) (add node02903 node00192)) (add (add (t Basis07.row205) (t Basis07.row206)) (add Basis07.row209 (t Basis07.row210)))) (add (add (add node01952 (t Basis07.row215)) (add (t Basis07.row216) (t Basis07.row217))) (add (add (t Basis07.row218) (t Basis07.row219)) (add node03019 (t Basis07.row223)))))))) (add (add (add (add (add (add Basis07.row225 (add (t Basis07.row225) Basis07.row228)) (add (add Basis07.row229 node00224) (add (t Basis07.row230) node03332))) (add (add (add Basis07.row235 Basis07.row237) (add node02536 Basis07.row243)) (add (add (t Basis07.row244) (t Basis07.row246)) (add node04244 (t Basis07.row249))))) (add (add (add (add Basis07.row253 (t Basis07.row254)) (add Basis07.row255 Basis07.row256)) (add (add (t Basis07.row257) Basis07.row258) (add (t Basis07.row260) node00366))) (add (add (add node01815 node03587) (add node02573 (t Basis07.row272))) (add (add node00952 node03083) (add node02537 node02037))))) (add (add (add (add (t Basis07.row282) (add (t Basis07.row283) node03237)) (add (add Basis07.row287 (t Basis07.row288)) (add Basis07.row289 Basis07.row290))) (add (add (add Basis07.row292 node02507) (add node00459 Basis07.row301)) (add (add Basis07.row302 node03446) (add (t Basis07.row309) (t Basis07.row312))))) (add (add (add (add node00150 (t Basis07.row315)) (add node00834 (t Basis07.row317))) (add (add node01192 node04292) (add node02538 node02697))) (add (add (add (t Basis07.row328) node00989) (add node01125 Basis07.row335)) (add (add (t Basis07.row335) (t Basis07.row336)) (add node01653 (t Basis07.row341))))))) (add (add (add (add (add Basis07.row342 (add node00082 node00784)) (add (add Basis07.row348 node00762) (add node02768 node03155))) (add (add (add node02411 Basis07.row357) (add node02330 Basis07.row362)) (add (add (t Basis07.row362) node03684) (add node03983 Basis07.row368)))) (add (add (add (add node02288 node01811) (add (t Basis07.row374) node01480)) (add (add (t Basis07.row377) node00520) (add Basis07.row383 (t Basis07.row385)))) (add (add (add Basis07.row387 Basis07.row388) (add Basis07.row389 node00483)) (add (add (t Basis07.row392) node04134) (add node00424 node00123))))) (add (add (add (add node03182 (add (t Basis07.row403) (t Basis07.row404))) (add (add Basis07.row408 Basis07.row409) (add (t Basis07.row409) Basis07.row411))) (add (add (add node01367 (t Basis07.row413)) (add Basis07.row416 node02833)) (add (add node01013 Basis07.row421) (add node02834 node00861)))) (add (add (add (add node00982 Basis07.row427) (add Basis07.row428 node04091)) (add (add Basis07.row432 Basis07.row433) (add Basis07.row435 (t Basis07.row437)))) (add (add (add Basis07.row438 node02520) (add node04063 (t Basis07.row446))) (add (add Basis07.row449 node02749) (add Basis07.row453 Basis07.row456)))))))) (add (add (add (add (add (add (add Basis07.row457 (add node03611 (t Basis07.row460))) (add (add Basis07.row461 node01253) (add node00524 node01014))) (add (add (add (t Basis07.row467) (t Basis07.row468)) (add node03768 node00316)) (add (add (t Basis07.row473) (t Basis07.row474)) (add node03351 (t Basis07.row477))))) (add (add (add (add (t Basis07.row479) node02003) (add node02939 node02576)) (add (add (t Basis07.row486) (t Basis07.row488)) (add node01069 node00824))) (add (add (add Basis07.row492 node02797) (add Basis07.row497 Basis07.row499)) (add (add (t Basis07.row500) node03532) (add node00759 Basis07.row506))))) (add (add (add (add Basis07.row507 (add node00099 Basis07.row510)) (add (add (t Basis07.row512) Basis07.row513) (add node02379 Basis07.row516))) (add (add (add node01188 node01072) (add node01356 (t Basis07.row522))) (add (add node03626 Basis07.row527) (add (t Basis07.row527) node01840)))) (add (add (add (add node02577 node00086) (add node04087 node02877)) (add (add node00871 node02862) (add Basis07.row541 (t Basis07.row541)))) (add (add (add node02110 (t Basis07.row546)) (add node00983 node00211)) (add (add Basis07.row553 node02058) (add node00111 Basis07.row558)))))) (add (add (add (add (add node03483 (add Basis07.row562 Basis07.row565)) (add (add Basis07.row566 node01962) (add Basis07.row569 Basis07.row572))) (add (add (add node01567 node03455) (add node00757 Basis07.row581)) (add (add node00321 node01777) (add (t Basis07.row586) Basis07.row587)))) (add (add (add (add Basis07.row588 Basis07.row589) (add node03309 (t Basis07.row592))) (add (add node02363 node03657) (add (t Basis07.row598) Basis07.row599))) (add (add (add Basis07.row600 Basis07.row601) (add (t Basis07.row601) node02464)) (add (add node01814 (t Basis07.row608)) (add node00262 node00794))))) (add (add (add (add (t Basis07.row614) (add node00602 node00667)) (add (add node02180 node02957) (add (t Basis07.row623) (t Basis07.row624)))) (add (add (add node04315 node00733) (add node00384 node01117)) (add (add Basis07.row636 (t Basis07.row636)) (add (t Basis07.row637) node02239)))) (add (add (add (add node00305 node01697) (add node01963 (t Basis07.row648))) (add (add Basis07.row649 Basis07.row651) (add Basis07.row654 node02993))) (add (add (add (t Basis07.row656) Basis07.row659) (add (t Basis07.row660) Basis07.row662)) (add (add (t Basis07.row662) node03926) (add node00528 Basis07.row670))))))) (add (add (add (add (add (add Basis07.row671 (add node02337 node02197)) (add (add node00185 node00811) (add Basis07.row681 node01847))) (add (add (add (t Basis07.row684) (t Basis07.row687)) (add Basis07.row688 Basis07.row689)) (add (add (t Basis07.row689) (t Basis07.row690)) (add Basis07.row692 Basis07.row693)))) (add (add (add (add node03008 (t Basis07.row696)) (add Basis07.row697 Basis07.row699)) (add (add node03317 Basis07.row704) (add node02199 Basis07.row707))) (add (add (add node03319 node01571) (add node01902 node01667)) (add (add (t Basis07.row719) node02119) (add node00233 (t Basis07.row727)))))) (add (add (add (add node02776 (add Basis07.row732 Basis07.row733)) (add (add node01372 Basis07.row737) (add node01322 node01057))) (add (add (add node01622 (t Basis07.row746)) (add (t Basis07.row747) node00263)) (add (add Basis07.row751 (t Basis07.row751)) (add Basis07.row753 (t Basis07.row753))))) (add (add (add (add (t Basis07.row754) node04025) (add (t Basis07.row759) Basis07.row760)) (add (add (t Basis07.row761) node00264) (add Basis07.row765 node02161))) (add (add (add node00035 node00389) (add node01202 node02610)) (add (add (t Basis07.row779) (t Basis07.row780)) (add node00700 Basis07.row783)))))) (add (add (add (add (add node00247 (add (t Basis07.row787) Basis07.row788)) (add (add Basis07.row790 node00279) (add node04076 node02249))) (add (add (add (t Basis07.row798) Basis07.row799) (add Basis07.row801 node00410)) (add (add node01530 node03712) (add (t Basis07.row808) node00986)))) (add (add (add (add (t Basis07.row814) (t Basis07.row815)) (add node00547 node03556)) (add (add (t Basis07.row823) (t Basis07.row824)) (add node03073 Basis07.row829))) (add (add (add node02786 Basis07.row833) (add node01019 Basis07.row838)) (add (add (t Basis07.row838) Basis07.row840) (add node01337 node00863))))) (add (add (add (add (add Basis07.row846 Basis07.row847) (add Basis07.row848 (t Basis07.row849))) (add (add Basis07.row850 (t Basis07.row851)) (add node00752 Basis07.row856))) (add (add (add (t Basis07.row857) (t Basis07.row859)) (add node00265 node00729)) (add (add node01119 (t Basis07.row866)) (add node00176 node00036)))) (add (add (add (add node03946 (t Basis07.row873)) (add node00177 node01002)) (add (add node03233 (t Basis07.row880)) (add Basis07.row881 Basis07.row882))) (add (add (add node03090 Basis07.row886) (add (t Basis07.row886) node00719)) (add (add node02272 node02423) (add Basis07.row893 node02787)))))))))

private theorem row202 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 202 (0, 0)) ((rowsAt 10).getD 202 (0, 0)) := by
  apply of_certificate witness202
  · decide +kernel
  · decide +kernel

private noncomputable def witness203 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add node00132 (add Basis07.row004 Basis07.row005)) (add (add Basis07.row007 (t Basis07.row007)) (add (t Basis07.row009) node02900))) (add (add (add node00591 (t Basis07.row014)) (add node00807 node00332)) (add (add (t Basis07.row018) node00842) (add Basis07.row023 node01921)))) (add (add (add node03618 (add (t Basis07.row030) (t Basis07.row031))) (add (add (t Basis07.row032) Basis07.row033) (add Basis07.row034 node00991))) (add (add (add node01497 node02476) (add Basis07.row042 (t Basis07.row042))) (add (add (t Basis07.row044) node03349) (add (t Basis07.row049) node02770))))) (add (add (add (add Basis07.row052 (add (t Basis07.row054) node00819)) (add (add (t Basis07.row058) node03972) (add (t Basis07.row062) (t Basis07.row064)))) (add (add (add Basis07.row066 node00661) (add node01220 node00221)) (add (add Basis07.row078 node01104) (add (t Basis07.row081) (t Basis07.row082))))) (add (add (add (t Basis07.row083) (add (t Basis07.row084) node03250)) (add (add node02598 node03965) (add (t Basis07.row093) node01986))) (add (add (add node00360 node02277) (add node02822 node00592)) (add (add node03562 node01739) (add (t Basis07.row111) (t Basis07.row112))))))) (add (add (add (add (add node01585 (add node03092 (t Basis07.row119))) (add (add (t Basis07.row120) (t Basis07.row121)) (add node00949 Basis07.row124))) (add (add (add node01597 node00771) (add Basis07.row130 Basis07.row134)) (add (add node03017 node01551) (add node01889 (t Basis07.row140))))) (add (add (add (t Basis07.row141) (add Basis07.row144 (t Basis07.row145))) (add (add node01821 (t Basis07.row148)) (add Basis07.row150 (t Basis07.row150)))) (add (add (add node02393 node01515) (add Basis07.row159 node00780)) (add (add node01165 node03910) (add node01648 (t Basis07.row169)))))) (add (add (add (add Basis07.row172 (add (t Basis07.row172) node00205)) (add (add (t Basis07.row175) (t Basis07.row177)) (add node01283 Basis07.row180))) (add (add (add Basis07.row181 node02047) (add (t Basis07.row184) node01692)) (add (add node00802 node01516) (add node02209 node00240)))) (add (add (add (add node00708 node02734) (add node00251 node00093)) (add (add node00826 Basis07.row206) (add node01477 node00393))) (add (add (add (t Basis07.row209) (t Basis07.row211)) (add node01172 node01223)) (add (add (t Basis07.row220) node03278) (add node04403 Basis07.row232))))))) (add (add (add (add (add (add (t Basis07.row232) (add Basis07.row234 Basis07.row235)) (add (add node01266 node00709) (add Basis07.row239 Basis07.row241))) (add (add (add (t Basis07.row242) Basis07.row245) (add Basis07.row246 (t Basis07.row250))) (add (add node01891 Basis07.row254) (add Basis07.row255 Basis07.row256)))) (add (add (add node00812 (add node01101 node01518)) (add (add node01557 node00398) (add Basis07.row268 Basis07.row269))) (add (add (add node03757 node02320) (add Basis07.row275 node02447)) (add (add node00539 node00206) (add Basis07.row282 (t Basis07.row282)))))) (add (add (add (add (t Basis07.row283) (add (t Basis07.row284) Basis07.row288)) (add (add node01972 Basis07.row291) (add (t Basis07.row293) node00628))) (add (add (add (t Basis07.row298) (t Basis07.row299)) (add Basis07.row301 (t Basis07.row306))) (add (add (t Basis07.row307) node02474) (add Basis07.row312 Basis07.row313)))) (add (add (add (add node04129 Basis07.row317) (add Basis07.row318 node03181)) (add (add node01084 node04213) (add node03795 node04045))) (add (add (add Basis07.row331 node00686) (add Basis07.row334 (t Basis07.row335))) (add (add (t Basis07.row336) Basis07.row337) (add node01828 (t Basis07.row340))))))) (add (add (add (add (add (t Basis07.row341) (add node01617 node00597)) (add (add (t Basis07.row346) node02488) (add node02865 Basis07.row353))) (add (add (add (t Basis07.row354) Basis07.row356) (add (t Basis07.row359) node03041)) (add (add (t Basis07.row363) Basis07.row365) (add node03522 node01335)))) (add (add (add node01688 (add node01257 Basis07.row375)) (add (add node01709 node00793) (add node03875 (t Basis07.row381)))) (add (add (add node03631 Basis07.row387) (add Basis07.row389 (t Basis07.row389))) (add (add Basis07.row390 node01277) (add Basis07.row398 (t Basis07.row398)))))) (add (add (add (add Basis07.row402 (add (t Basis07.row403) node04409)) (add (add Basis07.row410 node00227) (add node01367 node01896))) (add (add (add Basis07.row416 node02833) (add Basis07.row420 node01753)) (add (add (t Basis07.row423) node00910) (add (t Basis07.row426) node04308)))) (add (add (add (add (t Basis07.row433) node01030) (add node01073 node01742)) (add (add Basis07.row443 Basis07.row444) (add (t Basis07.row444) (t Basis07.row447)))) (add (add (add node00367 node02960) (add Basis07.row454 Basis07.row455)) (add (add node01470 (t Basis07.row458)) (add (t Basis07.row460) (t Basis07.row461))))))))) (add (add (add (add (add (add (add node02134 (add node04064 (t Basis07.row466))) (add (add node01359 Basis07.row469) (add node02802 node04414))) (add (add (add Basis07.row478 Basis07.row479) (add node00738 (t Basis07.row481))) (add (add Basis07.row484 node02189) (add node01069 node00885)))) (add (add (add node04493 (add (t Basis07.row495) node02170)) (add (add node00110 node00642) (add node04222 node01985))) (add (add (add node01693 node01368) (add (t Basis07.row512) node00174)) (add (add node01628 Basis07.row516) (add node03742 Basis07.row520))))) (add (add (add (add node01356 (add (t Basis07.row524) (t Basis07.row525))) (add (add (t Basis07.row527) node01929) (add Basis07.row530 Basis07.row532))) (add (add (add node02191 Basis07.row537) (add node00544 Basis07.row539)) (add (add Basis07.row540 (t Basis07.row541)) (add node00526 node00175)))) (add (add (add (add node02295 node03691) (add (t Basis07.row553) (t Basis07.row554))) (add (add (t Basis07.row555) Basis07.row557) (add Basis07.row558 Basis07.row559))) (add (add (add Basis07.row560 node00002) (add Basis07.row565 node03307)) (add (add node01016 node01348) (add (t Basis07.row573) Basis07.row575)))))) (add (add (add (add (add Basis07.row578 (add node03535 (t Basis07.row586))) (add (add node00024 (t Basis07.row589)) (add node00212 node02070))) (add (add (add node02724 node00956) (add node01262 Basis07.row602)) (add (add node01746 node00000) (add node00183 node01260)))) (add (add (add Basis07.row612 (add (t Basis07.row612) (t Basis07.row613))) (add (add node03989 Basis07.row617) (add (t Basis07.row618) Basis07.row620))) (add (add (add node02957 node01569) (add Basis07.row626 Basis07.row628)) (add (add (t Basis07.row628) node00567) (add node02010 Basis07.row634))))) (add (add (add (add (t Basis07.row636) (add (t Basis07.row637) Basis07.row638)) (add (add node02299 node01000) (add Basis07.row643 Basis07.row645))) (add (add (add (t Basis07.row645) Basis07.row648) (add Basis07.row649 node00277)) (add (add Basis07.row652 Basis07.row653) (add node00577 Basis07.row657)))) (add (add (add (add node00407 (t Basis07.row659)) (add (t Basis07.row660) node03265)) (add (add node00199 (t Basis07.row665)) (add (t Basis07.row667) node01345))) (add (add (add Basis07.row670 Basis07.row671) (add (t Basis07.row671) (t Basis07.row672))) (add (add Basis07.row673 node00246) (add node00886 (t Basis07.row678)))))))) (add (add (add (add (add (add node03333 (add node02157 (t Basis07.row684))) (add (add (t Basis07.row686) Basis07.row687) (add (t Basis07.row688) (t Basis07.row689)))) (add (add (add node02631 Basis07.row693) (add (t Basis07.row693) node01580)) (add (add node01085 node01173) (add (t Basis07.row702) (t Basis07.row706))))) (add (add (add Basis07.row708 (add (t Basis07.row708) (t Basis07.row709))) (add (add node01304 node00187) (add (t Basis07.row715) (t Basis07.row717)))) (add (add (add (t Basis07.row718) Basis07.row719) (add node00386 Basis07.row723)) (add (add Basis07.row724 (t Basis07.row724)) (add node02075 node00326))))) (add (add (add (add node01875 (add node03608 node02301)) (add (add (t Basis07.row740) node02857) (add node01182 (t Basis07.row744)))) (add (add (add node02579 node00296) (add node01860 node02383)) (add (add node00988 Basis07.row758) (add Basis07.row759 Basis07.row761)))) (add (add (add (add Basis07.row762 (t Basis07.row762)) (add (t Basis07.row764) node00579)) (add (add node00388 node01733) (add (t Basis07.row771) Basis07.row773))) (add (add (add (t Basis07.row773) (t Basis07.row774)) (add Basis07.row775 Basis07.row776)) (add (add (t Basis07.row778) node03431) (add Basis07.row783 Basis07.row784)))))) (add (add (add (add (add Basis07.row785 (add Basis07.row786 node00390)) (add (add node01670 Basis07.row790) (add Basis07.row791 Basis07.row792))) (add (add (add Basis07.row793 Basis07.row794) (add Basis07.row795 node01589)) (add (add node03643 (t Basis07.row801)) (add node02550 node02499)))) (add (add (add node03621 (add Basis07.row809 Basis07.row810)) (add (add node02017 node00878) (add node02672 node00558))) (add (add (add (t Basis07.row818) node03219) (add node01793 node01059)) (add (add node00888 node00144) (add node01233 node02925))))) (add (add (add (add node01019 (add Basis07.row837 (t Basis07.row838))) (add (add (t Basis07.row842) node00975) (add node00495 Basis07.row847))) (add (add (add (t Basis07.row849) node04326) (add node00752 node02864)) (add (add (t Basis07.row857) (t Basis07.row859)) (add node00265 node03280)))) (add (add (add (add node01500 Basis07.row869) (add node04246 node01264)) (add (add (t Basis07.row876) node03324) (add node00839 node02127))) (add (add (add node01256 node00605) (add node00960 (t Basis07.row890))) (add (add Basis07.row891 node02603) (add Basis07.row894 Basis07.row895)))))))))

private theorem row203 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 203 (0, 0)) ((rowsAt 10).getD 203 (0, 0)) := by
  apply of_certificate witness203
  · decide +kernel
  · decide +kernel

private noncomputable def witness204 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row056

private theorem row204 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 204 (0, 0)) ((rowsAt 10).getD 204 (0, 0)) := by
  apply of_certificate witness204
  · decide +kernel
  · decide +kernel

private noncomputable def witness205 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row487

private theorem row205 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 205 (0, 0)) ((rowsAt 10).getD 205 (0, 0)) := by
  apply of_certificate witness205
  · decide +kernel
  · decide +kernel

private noncomputable def witness206 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add node00790 (add node01241 node00776)) (add (add node00606 Basis07.row007) (add (t Basis07.row007) (t Basis07.row009)))) (add (add (add (t Basis07.row010) (t Basis07.row011)) (add Basis07.row012 node03665)) (add (add node01741 node01941) (add node00114 node00178)))) (add (add (add (add node03245 node02323) (add (t Basis07.row028) (t Basis07.row029))) (add (add (t Basis07.row031) (t Basis07.row032)) (add Basis07.row033 node02953))) (add (add (add node03669 (t Basis07.row041)) (add (t Basis07.row042) node00607)) (add (add node03003 Basis07.row050) (add Basis07.row051 (t Basis07.row052)))))) (add (add (add (add (add (t Basis07.row053) (t Basis07.row054)) (add (t Basis07.row055) (t Basis07.row056))) (add (add node01579 node03862) (add node01294 node00670))) (add (add (add node00661 node04080) (add node00269 (t Basis07.row074))) (add (add (t Basis07.row076) (t Basis07.row077)) (add (t Basis07.row078) (t Basis07.row079))))) (add (add (add (add Basis07.row080 node00308) (add node00747 node00377)) (add (add (t Basis07.row089) Basis07.row091) (add Basis07.row092 node04339))) (add (add (add node01986 (t Basis07.row098)) (add Basis07.row100 node02277)) (add (add node00753 node02587) (add node03335 Basis07.row114)))))) (add (add (add (add (add Basis07.row115 (add (t Basis07.row115) Basis07.row118)) (add (add node00879 Basis07.row122) (add (t Basis07.row122) Basis07.row124))) (add (add (add (t Basis07.row125) (t Basis07.row128)) (add (t Basis07.row130) node03506)) (add (add Basis07.row134 node03954) (add (t Basis07.row140) (t Basis07.row141))))) (add (add (add (add node02024 (t Basis07.row145)) (add node02084 (t Basis07.row148))) (add (add Basis07.row149 node02607) (add node02355 node00480))) (add (add (add (t Basis07.row156) (t Basis07.row157)) (add node00780 node03154)) (add (add node00180 node01648) (add node01297 (t Basis07.row171)))))) (add (add (add (add (add node02307 (t Basis07.row175)) (add Basis07.row176 node00334)) (add (add node02046 (t Basis07.row181)) (add Basis07.row183 (t Basis07.row184)))) (add (add (add Basis07.row188 Basis07.row189) (add (t Basis07.row189) node00271)) (add (add node02354 Basis07.row196) (add node00251 node00748)))) (add (add (add (add node01387 node00826) (add node01599 node03867)) (add (add node01334 Basis07.row212) (add Basis07.row213 node00417))) (add (add (add node01153 Basis07.row220) (add Basis07.row221 node04078)) (add (add Basis07.row224 Basis07.row225) (add (t Basis07.row225) node01601))))))) (add (add (add (add (add (add Basis07.row231 (add node02824 node02185)) (add (add Basis07.row237 Basis07.row241) (add node03913 node00396))) (add (add (add Basis07.row247 Basis07.row248) (add Basis07.row249 Basis07.row250)) (add (add node00518 node00750) (add node01464 node03443)))) (add (add (add (add node03000 (t Basis07.row261)) (add (t Basis07.row262) node01815)) (add (add node03623 (t Basis07.row267)) (add node00242 (t Basis07.row270)))) (add (add (add Basis07.row271 (t Basis07.row272)) (add node02447 node01804)) (add (add (t Basis07.row280) (t Basis07.row281)) (add Basis07.row283 Basis07.row284))))) (add (add (add (add (add Basis07.row285 Basis07.row288) (add Basis07.row290 node01467)) (add (add node01046 node03492) (add Basis07.row300 node00022))) (add (add (add Basis07.row303 Basis07.row304) (add (t Basis07.row304) (t Basis07.row305))) (add (add Basis07.row306 node01768) (add node00047 node00290)))) (add (add (add (add node01091 Basis07.row313) (add node03981 node00834)) (add (add node03863 Basis07.row322) (add Basis07.row325 Basis07.row326))) (add (add (add node00013 node03148) (add node02872 node00979)) (add (add node00930 Basis07.row338) (add node02923 (t Basis07.row342))))))) (add (add (add (add (add (add (t Basis07.row343) node02053) (add Basis07.row347 node01988)) (add (add Basis07.row350 node02596) (add (t Basis07.row352) (t Basis07.row354)))) (add (add (add (t Basis07.row355) Basis07.row356) (add (t Basis07.row358) node03764)) (add (add node01214 node00274) (add (t Basis07.row368) Basis07.row369)))) (add (add (add (add (t Basis07.row370) Basis07.row371) (add Basis07.row372 node04407)) (add (add node02029 node00793) (add Basis07.row379 Basis07.row380))) (add (add (add (t Basis07.row380) node01655) (add (t Basis07.row385) node00194)) (add (add (t Basis07.row387) (t Basis07.row388)) (add Basis07.row392 Basis07.row394))))) (add (add (add (add (add Basis07.row397 (t Basis07.row399)) (add node00720 node02708)) (add (add node00445 (t Basis07.row406)) (add (t Basis07.row407) Basis07.row410))) (add (add (add (t Basis07.row410) node01367) (add Basis07.row414 Basis07.row415)) (add (add (t Basis07.row415) Basis07.row417) (add (t Basis07.row417) Basis07.row419)))) (add (add (add (add (t Basis07.row422) Basis07.row423) (add Basis07.row424 (t Basis07.row425))) (add (add Basis07.row427 node00552) (add node00338 node02616))) (add (add (add Basis07.row435 Basis07.row436) (add (t Basis07.row436) node03170)) (add (add node01344 node00084) (add node01399 node04455)))))))) (add (add (add (add (add (add (add node00339 (add (t Basis07.row454) Basis07.row456)) (add (add Basis07.row457 (t Basis07.row457)) (add Basis07.row459 node00153))) (add (add (add (t Basis07.row463) node03450) (add (t Basis07.row467) node01093)) (add (add node03276 node02873) (add Basis07.row476 Basis07.row477)))) (add (add (add (add node01542 node02216) (add Basis07.row485 node02494)) (add (add node02966 node03452) (add node03115 node02004))) (add (add (add Basis07.row498 node00110) (add (t Basis07.row501) (t Basis07.row502))) (add (add node02435 (t Basis07.row505)) (add Basis07.row507 node01420))))) (add (add (add (add (add Basis07.row510 (t Basis07.row511)) (add Basis07.row513 node02379)) (add (add node01015 node04309) (add (t Basis07.row520) node01523))) (add (add (add Basis07.row527 (t Basis07.row527)) (add Basis07.row528 Basis07.row529)) (add (add Basis07.row530 node02397) (add Basis07.row534 (t Basis07.row534))))) (add (add (add (add node01774 node01108) (add node01063 node00741)) (add (add Basis07.row545 (t Basis07.row547)) (add node02705 node02627))) (add (add (add (t Basis07.row552) (t Basis07.row553)) (add (t Basis07.row554) (t Basis07.row555))) (add (add Basis07.row556 (t Basis07.row556)) (add (t Basis07.row557) (t Basis07.row560))))))) (add (add (add (add (add (add Basis07.row561 node04143) (add node02897 (t Basis07.row566))) (add (add (t Basis07.row567) node00196) (add Basis07.row572 node00087))) (add (add (add node02319 node00846) (add (t Basis07.row581) (t Basis07.row582))) (add (add node00682 Basis07.row586) (add (t Basis07.row587) (t Basis07.row588))))) (add (add (add (add node00032 node01422) (add (t Basis07.row594) node01116)) (add (add Basis07.row598 (t Basis07.row598)) (add Basis07.row599 Basis07.row600))) (add (add (add node00322 Basis07.row606) (add node01325 node00815)) (add (add node02115 Basis07.row613) (add node00913 Basis07.row616))))) (add (add (add (add (add node00159 (t Basis07.row618)) (add Basis07.row620 node00184)) (add (add node00716 node00166) (add node01205 node02335))) (add (add (add node00900 (t Basis07.row631)) (add Basis07.row632 node04032)) (add (add (t Basis07.row636) (t Basis07.row637)) (add Basis07.row638 Basis07.row639)))) (add (add (add (add Basis07.row640 node00854) (add node01095 node01799)) (add (add node01040 node02132) (add Basis07.row650 node01812))) (add (add (add node01078 node00577) (add node04258 node01243)) (add (add node02196 (t Basis07.row664)) (add node02741 (t Basis07.row667)))))))) (add (add (add (add (add (add Basis07.row670 (add (t Basis07.row670) node00373)) (add (add node01975 node00185) (add node02888 node00347))) (add (add (add Basis07.row682 node02141) (add node02855 node00008)) (add (add node04385 Basis07.row695) (add node01423 node04234)))) (add (add (add (add (t Basis07.row700) node01735) (add node04085 Basis07.row706)) (add (add Basis07.row708 node03461) (add node01438 node01864))) (add (add (add node01490 node01062) (add (t Basis07.row720) (t Basis07.row722))) (add (add (t Basis07.row723) (t Basis07.row725)) (add (t Basis07.row726) Basis07.row727))))) (add (add (add (add (add node00689 node01694) (add (t Basis07.row731) Basis07.row732)) (add (add node01875 Basis07.row735) (add node01322 node03929))) (add (add (add Basis07.row742 Basis07.row743) (add (t Basis07.row743) node02245)) (add (add node01968 (t Basis07.row750)) (add node01473 node03645)))) (add (add (add (add (t Basis07.row759) node04322) (add node01851 (t Basis07.row766))) (add (add (t Basis07.row767) Basis07.row768) (add Basis07.row770 node04278))) (add (add (add node01463 Basis07.row777) (add Basis07.row779 node00409)) (add (add node04028 (t Basis07.row783)) (add (t Basis07.row785) node04380)))))) (add (add (add (add (add (add node02316 node01434) (add Basis07.row796 Basis07.row797)) (add (add (t Basis07.row797) node03966) (add (t Basis07.row801) node01989))) (add (add (add node01530 node01627) (add (t Basis07.row808) node02523)) (add (add node00218 node01800) (add Basis07.row818 node01109)))) (add (add (add (add node00919 Basis07.row822) (add Basis07.row823 Basis07.row824)) (add (add (t Basis07.row825) node00888) (add node00690 Basis07.row831))) (add (add (add node01233 node00691) (add node03141 (t Basis07.row836))) (add (add (t Basis07.row837) (t Basis07.row839)) (add Basis07.row840 Basis07.row841))))) (add (add (add (add (add Basis07.row844 (t Basis07.row844)) (add (t Basis07.row845) node01216)) (add (add node00356 node01636) (add Basis07.row853 node01425))) (add (add (add node01673 node00864) (add node00473 Basis07.row860)) (add (add (t Basis07.row862) (t Basis07.row865)) (add node01500 Basis07.row869)))) (add (add (add (add Basis07.row870 node01532) (add (t Basis07.row873) Basis07.row874)) (add (add Basis07.row875 node02949) (add (t Basis07.row879) (t Basis07.row880)))) (add (add (add Basis07.row881 Basis07.row883) (add (t Basis07.row883) node02779)) (add (add Basis07.row887 node02253) (add node00668 Basis07.row895)))))))))

private theorem row206 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 206 (0, 0)) ((rowsAt 10).getD 206 (0, 0)) := by
  apply of_certificate witness206
  · decide +kernel
  · decide +kernel

private noncomputable def witness207 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add node01148 (add node02793 node03899)) (add (add node03971 (t Basis07.row017)) (add (t Basis07.row019) (t Basis07.row020)))) (add (add (add node02782 node00817) (add node02026 Basis07.row028)) (add (add node01432 node00307) (add node00090 node03814)))) (add (add (add (t Basis07.row039) (add node00220 node00284)) (add (add node01475 (t Basis07.row045)) (add Basis07.row046 node02619))) (add (add (add (t Basis07.row049) Basis07.row051) (add (t Basis07.row054) node02792)) (add (add node02466 node00116) (add node01103 node01755))))) (add (add (add (add node02306 (add node01759 node02740)) (add (add Basis07.row071 Basis07.row072) (add node01327 (t Basis07.row076)))) (add (add (add node03829 node00055) (add (t Basis07.row084) node03905)) (add (add node02813 node01021) (add node02225 node03753)))) (add (add (add (add node02182 node01631) (add node01760 node00592)) (add (add node01819 node04008) (add node02674 Basis07.row112))) (add (add (add node01993 node01087) (add node00297 (t Basis07.row119))) (add (add (t Basis07.row120) (t Basis07.row121)) (add Basis07.row122 (t Basis07.row124))))))) (add (add (add (add (add node01795 (add (t Basis07.row128) (t Basis07.row129))) (add (add (t Basis07.row132) Basis07.row133) (add (t Basis07.row133) node04205))) (add (add (add Basis07.row140 node02176) (add node00107 node00438)) (add (add node01024 node00287) (add Basis07.row152 Basis07.row153)))) (add (add (add (add Basis07.row154 Basis07.row156) (add node00976 (t Basis07.row158))) (add (add Basis07.row160 Basis07.row162) (add (t Basis07.row162) node03252))) (add (add (add Basis07.row166 (t Basis07.row168)) (add node03832 node02726)) (add (add node02481 node00118) (add node00334 node01283))))) (add (add (add (add node00585 (add node00239 (t Basis07.row183))) (add (add (t Basis07.row184) node01472) (add Basis07.row188 Basis07.row189))) (add (add (add Basis07.row191 node01437) (add node00240 node01765)) (add (add Basis07.row197 (t Basis07.row199)) (add (t Basis07.row200) (t Basis07.row201))))) (add (add (add (add node04442 (t Basis07.row205)) (add node01477 Basis07.row209)) (add (add Basis07.row210 Basis07.row211) (add (t Basis07.row211) (t Basis07.row212)))) (add (add (add node01411 (t Basis07.row216)) (add node02760 node03585)) (add (add node03551 Basis07.row232) (add node00663 Basis07.row235))))))) (add (add (add (add (add (add node01266 (add node00709 Basis07.row239)) (add (add node01089 node01026) (add node02484 node01176))) (add (add (add node02146 (t Basis07.row250)) (add Basis07.row251 node01244)) (add (add node02446 (t Basis07.row256)) (add (t Basis07.row257) (t Basis07.row259))))) (add (add (add node00679 (add node01557 (t Basis07.row265))) (add (add node00254 node00058) (add node00772 Basis07.row274))) (add (add (add Basis07.row277 (t Basis07.row278)) (add (t Basis07.row280) node00501)) (add (add node01414 (t Basis07.row289)) (add Basis07.row290 node00311))))) (add (add (add (add Basis07.row293 (add node02035 node00207)) (add (add node03838 node01288) (add node00695 node00792))) (add (add (add Basis07.row307 Basis07.row308) (add node00737 node03198)) (add (add node00808 node01175) (add node01192 (t Basis07.row323))))) (add (add (add (add (t Basis07.row324) Basis07.row325) (add Basis07.row326 node00803)) (add (add (t Basis07.row328) node00541) (add (t Basis07.row330) Basis07.row332))) (add (add (add node00651 node03682) (add node02789 (t Basis07.row340))) (add (add (t Basis07.row343) Basis07.row344) (add Basis07.row345 Basis07.row347)))))) (add (add (add (add (add (t Basis07.row348) (add (t Basis07.row349) node02865)) (add (add node03762 node01415) (add Basis07.row359 Basis07.row362))) (add (add (add Basis07.row365 node01745) (add node01561 Basis07.row370)) (add (add Basis07.row371 (t Basis07.row372)) (add node00048 node02313)))) (add (add (add (add (t Basis07.row377) node03875) (add Basis07.row382 Basis07.row383)) (add (add node04408 Basis07.row387) (add node01562 (t Basis07.row389)))) (add (add (add Basis07.row390 Basis07.row392) (add (t Basis07.row394) (t Basis07.row396))) (add (add (t Basis07.row397) (t Basis07.row399)) (add (t Basis07.row400) node03843))))) (add (add (add (add (t Basis07.row403) (add (t Basis07.row404) node01482)) (add (add node00574 node00751) (add Basis07.row411 node01367))) (add (add (add Basis07.row415 (t Basis07.row415)) (add node02025 (t Basis07.row418))) (add (add node00521 node00173) (add node03091 node02377)))) (add (add (add (add node00338 node02616) (add node03377 node01073)) (add (add node00259 node01344) (add Basis07.row444 (t Basis07.row444)))) (add (add (add node00428 Basis07.row447) (add Basis07.row448 (t Basis07.row448))) (add (add (t Basis07.row449) Basis07.row450) (add Basis07.row451 Basis07.row453)))))))) (add (add (add (add (add (add (add node02349 (add node02210 node02997)) (add (add Basis07.row460 Basis07.row461) (add node01508 Basis07.row464))) (add (add (add node03845 node02809) (add node00614 node02644)) (add (add (t Basis07.row478) (t Basis07.row479)) (add (t Basis07.row481) Basis07.row483)))) (add (add (add Basis07.row487 (add node02989 node00824)) (add (add node03685 (t Basis07.row496)) (add (t Basis07.row497) node00850))) (add (add (add node02815 node00370) (add node01286 node02581)) (add (add node01693 Basis07.row510) (add (t Basis07.row513) node03304))))) (add (add (add (add node03384 (add Basis07.row520 node02469)) (add (add node01523 node01178) (add (t Basis07.row526) node01840))) (add (add (add node00156 node01721) (add node04446 (t Basis07.row535))) (add (add (t Basis07.row536) node00544) (add node03209 Basis07.row542)))) (add (add (add (add node02135 Basis07.row545) (add node01052 node00195)) (add (add (t Basis07.row552) (t Basis07.row553)) (add (t Basis07.row554) (t Basis07.row555)))) (add (add (add Basis07.row556 Basis07.row559) (add Basis07.row561 (t Basis07.row562))) (add (add node01298 Basis07.row567) (add (t Basis07.row567) node01016)))))) (add (add (add (add (add (t Basis07.row570) (add node02315 node00742)) (add (add Basis07.row578 node01197) (add node01924 Basis07.row583))) (add (add (add node00955 (t Basis07.row588)) (add Basis07.row590 node03564)) (add (add node01698 node03161) (add node01146 node02059)))) (add (add (add (add Basis07.row601 Basis07.row603) (add node00764 node02193)) (add (add Basis07.row609 (t Basis07.row609)) (add node01743 node04180))) (add (add (add Basis07.row615 Basis07.row616) (add node00060 node00576)) (add (add Basis07.row623 node02754) (add node00671 node02335))))) (add (add (add (add (t Basis07.row629) (add (t Basis07.row631) node00384)) (add (add Basis07.row635 (t Basis07.row636)) (add (t Basis07.row637) node02239))) (add (add (add (t Basis07.row640) (t Basis07.row642)) (add (t Basis07.row643) Basis07.row645)) (add (add (t Basis07.row645) Basis07.row647) (add (t Basis07.row647) Basis07.row651)))) (add (add (add (add Basis07.row652 Basis07.row653) (add node01096 (t Basis07.row655))) (add (add Basis07.row656 node01845) (add Basis07.row659 Basis07.row660))) (add (add (add node02941 Basis07.row663) (add node02438 (t Basis07.row665))) (add (add node00528 node03030) (add node00886 node01079))))))) (add (add (add (add (add (add node01868 (add Basis07.row682 (t Basis07.row682))) (add (add node03316 node00734) (add (t Basis07.row688) Basis07.row689))) (add (add (add (t Basis07.row689) Basis07.row691) (add node01724 Basis07.row697)) (add (add node01229 node04148) (add node00324 node01441)))) (add (add (add node00929 (add node03780 node00293)) (add (add node01625 node02380) (add (t Basis07.row719) Basis07.row720))) (add (add (add Basis07.row721 Basis07.row722) (add node00232 node01041)) (add (add Basis07.row726 Basis07.row728) (add node01694 (t Basis07.row731)))))) (add (add (add (add node03269 (add node01867 (t Basis07.row736))) (add (add Basis07.row737 node00216) (add node01057 node02544))) (add (add (add node04374 Basis07.row746) (add node01781 Basis07.row749)) (add (add node01861 node02549) (add node00327 (t Basis07.row755))))) (add (add (add (add Basis07.row757 Basis07.row758) (add Basis07.row759 node01180)) (add (add (t Basis07.row764) node00387) (add node01573 Basis07.row772))) (add (add (add (t Basis07.row772) (t Basis07.row776)) (add node00984 node02014)) (add (add node00493 node00453) (add (t Basis07.row785) (t Basis07.row786))))))) (add (add (add (add (add (t Basis07.row787) (add (t Basis07.row788) Basis07.row789)) (add (add Basis07.row790 Basis07.row791) (add Basis07.row792 (t Basis07.row794)))) (add (add (add Basis07.row797 node00925) (add (t Basis07.row801) Basis07.row802)) (add (add Basis07.row803 (t Basis07.row807)) (add Basis07.row808 Basis07.row809)))) (add (add (add (add (t Basis07.row809) node02017) (add Basis07.row813 Basis07.row815)) (add (add (t Basis07.row815) Basis07.row818) (add node03887 Basis07.row821))) (add (add (add node01793 Basis07.row824) (add node00685 node02529)) (add (add node01233 node00691) (add node03125 node01006))))) (add (add (add (add node00940 (add node00692 (t Basis07.row844))) (add (add node04196 node01630) (add node01636 node00623))) (add (add (add Basis07.row854 node00089) (add node02019 node00729)) (add (add node01119 Basis07.row865) (add node01500 node00176)))) (add (add (add (add node01590 Basis07.row872) (add Basis07.row873 (t Basis07.row873))) (add (add node01918 node04033) (add (t Basis07.row879) (t Basis07.row881)))) (add (add (add node01135 node01256) (add (t Basis07.row886) node00719)) (add (add node01082 node02501) (add Basis07.row892 node00669)))))))))

private theorem row207 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 207 (0, 0)) ((rowsAt 10).getD 207 (0, 0)) := by
  apply of_certificate witness207
  · decide +kernel
  · decide +kernel

private noncomputable def witness208 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row057

private theorem row208 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 208 (0, 0)) ((rowsAt 10).getD 208 (0, 0)) := by
  apply of_certificate witness208
  · decide +kernel
  · decide +kernel

private noncomputable def witness209 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add node01884 (add node00132 Basis07.row003)) (add (add node00606 node01102) (add (t Basis07.row007) node02900))) (add (add (add node03509 node00190) (add Basis07.row017 node03289)) (add (add Basis07.row021 (t Basis07.row021)) (add node02090 node04261)))) (add (add (add node03010 (add node01432 node00307)) (add (add (t Basis07.row034) (t Basis07.row036)) (add Basis07.row037 Basis07.row038))) (add (add (add (t Basis07.row039) node00220) (add node02309 (t Basis07.row044))) (add (add (t Basis07.row047) Basis07.row048) (add Basis07.row049 (t Basis07.row050)))))) (add (add (add (add node02223 (add node00510 node03583)) (add (add node01700 node01103) (add (t Basis07.row062) node00073))) (add (add (add (t Basis07.row070) Basis07.row071) (add (t Basis07.row075) Basis07.row076)) (add (add node01923 node04243) (add node01595 (t Basis07.row085))))) (add (add (add (t Basis07.row086) (add Basis07.row087 Basis07.row088)) (add (add (t Basis07.row088) node01086) (add node00512 node02276))) (add (add (add node00009 (t Basis07.row098)) (add (t Basis07.row099) (t Basis07.row100))) (add (add node01328 Basis07.row104) (add node01338 node03193)))))) (add (add (add (add (add node03635 (add Basis07.row113 node02618)) (add (add node00286 node00948) (add (t Basis07.row118) node02317))) (add (add (add node00170 (t Basis07.row124)) (add Basis07.row125 Basis07.row126)) (add (add Basis07.row127 node03907) (add node03908 (t Basis07.row134))))) (add (add (add (t Basis07.row135) (add node01551 Basis07.row139)) (add (add node00736 node02600) (add (t Basis07.row146) Basis07.row149))) (add (add (add (t Basis07.row150) (t Basis07.row152)) (add Basis07.row153 Basis07.row154)) (add (add node03251 node00780) (add (t Basis07.row161) Basis07.row163))))) (add (add (add (add Basis07.row164 (add (t Basis07.row166) (t Basis07.row167))) (add (add node00977 (t Basis07.row174)) (add (t Basis07.row177) node03171))) (add (add (add node00239 node02047) (add (t Basis07.row187) node01320)) (add (add node00162 node02209) (add Basis07.row194 node02530)))) (add (add (add (t Basis07.row197) (add Basis07.row198 node00893)) (add (add node01696 node04442) (add Basis07.row206 (t Basis07.row207)))) (add (add (add node01633 (t Basis07.row210)) (add Basis07.row213 node03833)) (add (add node01453 Basis07.row221) (add node01824 (t Basis07.row223)))))))) (add (add (add (add (add (add Basis07.row225 (add (t Basis07.row225) node01274)) (add (add Basis07.row230 node00365) (add (t Basis07.row232) node00663))) (add (add (add (t Basis07.row235) (t Basis07.row236)) (add node01651 node02312)) (add (add Basis07.row241 (t Basis07.row241)) (add Basis07.row244 Basis07.row245)))) (add (add (add node01176 (add node01556 node03804)) (add (add node01244 node00046) (add node04055 node00679))) (add (add (add Basis07.row263 node01815) (add node01131 node02147)) (add (add node01413 Basis07.row275) (add (t Basis07.row277) (t Basis07.row278)))))) (add (add (add (add (t Basis07.row280) (add node03500 (t Basis07.row284))) (add (add node04193 node01972) (add (t Basis07.row292) (t Basis07.row294)))) (add (add (add Basis07.row297 node03746) (add (t Basis07.row300) (t Basis07.row301))) (add (add Basis07.row303 (t Basis07.row303)) (add node03917 Basis07.row308)))) (add (add (add node00047 (add node00737 node01091)) (add (add (t Basis07.row315) Basis07.row316) (add node03840 (t Basis07.row319)))) (add (add (add node02982 (t Basis07.row323)) (add (t Basis07.row324) Basis07.row325)) (add (add (t Basis07.row325) node00541) (add node00906 node00686)))))) (add (add (add (add (add node00980 (add node00930 Basis07.row338)) (add (add node02956 node01316) (add node01309 node01177))) (add (add (add node03424 (t Basis07.row349)) (add (t Basis07.row350) Basis07.row351)) (add (add Basis07.row353 Basis07.row354) (add node00611 node01878)))) (add (add (add Basis07.row360 (add node03878 node03592)) (add (add node00845 node02505) (add (t Basis07.row370) (t Basis07.row371)))) (add (add (add (t Basis07.row372) Basis07.row373) (add node01480 node00793)) (add (add node02816 (t Basis07.row380)) (add (t Basis07.row381) (t Basis07.row382)))))) (add (add (add (add (t Basis07.row383) (add Basis07.row384 Basis07.row387)) (add (add (t Basis07.row387) (t Basis07.row390)) (add node00423 node00629))) (add (add (add (t Basis07.row394) node00763) (add node04287 (t Basis07.row401))) (add (add (t Basis07.row403) (t Basis07.row406)) (add node02490 Basis07.row411)))) (add (add (add (add Basis07.row412 node00337) (add (t Basis07.row414) node04192)) (add (add node01204 node01833) (add (t Basis07.row423) Basis07.row425))) (add (add (add (t Basis07.row425) node00426) (add node01483 node03078)) (add (add (t Basis07.row435) (t Basis07.row436)) (add Basis07.row438 (t Basis07.row439))))))))) (add (add (add (add (add (add (add Basis07.row442 (add node03379 Basis07.row445)) (add (add node02083 Basis07.row448) (add (t Basis07.row448) Basis07.row452))) (add (add (add (t Basis07.row455) (t Basis07.row456)) (add node04376 (t Basis07.row460))) (add (add node02134 node00706) (add Basis07.row469 (t Basis07.row470))))) (add (add (add (t Basis07.row471) (add Basis07.row472 node02727)) (add (add node03351 Basis07.row478) (add Basis07.row479 (t Basis07.row479)))) (add (add (add (t Basis07.row481) node03287) (add node02494 node01069)) (add (add node00824 node03274) (add (t Basis07.row494) (t Basis07.row495)))))) (add (add (add (add (t Basis07.row497) (add node01076 node00642)) (add (add Basis07.row503 Basis07.row504) (add Basis07.row505 (t Basis07.row507)))) (add (add (add node02844 Basis07.row510) (add node00017 node02378)) (add (add node00210 node01164) (add node00505 node02155)))) (add (add (add node03533 (add node00069 node00849)) (add (add node02108 (t Basis07.row531)) (add Basis07.row532 node03688))) (add (add (add (t Basis07.row536) (t Basis07.row539)) (add node01036 Basis07.row542)) (add (add node02540 (t Basis07.row546)) (add node03024 (t Basis07.row550))))))) (add (add (add (add (add node04142 (add node00566 Basis07.row557)) (add (add node02112 node00934) (add node02169 node02113))) (add (add (add Basis07.row565 node01381) (add Basis07.row568 Basis07.row569)) (add (add node01486 node00087) (add node03881 node00757)))) (add (add (add Basis07.row580 (add node02072 node00321)) (add (add Basis07.row585 node00899) (add (t Basis07.row589) (t Basis07.row590)))) (add (add (add node00829 node02114) (add (t Basis07.row598) node00527)) (add (add Basis07.row601 (t Basis07.row601)) (add (t Basis07.row603) Basis07.row606))))) (add (add (add (add Basis07.row608 (add node00815 node01743)) (add (add node00794 node00467) (add node00602 Basis07.row618))) (add (add (add Basis07.row620 node03776) (add node00166 node01205)) (add (add node02335 Basis07.row630) (add node02010 node01179)))) (add (add (add (t Basis07.row636) (add (t Basis07.row637) node02239)) (add (add node00305 Basis07.row642) (add (t Basis07.row643) node01665))) (add (add (add node01040 node01691) (add Basis07.row651 node03426)) (add (add node02993 node00112) (add node00407 node02775))))))) (add (add (add (add (add (add node00928 (add (t Basis07.row662) node00245)) (add (add (t Basis07.row666) (t Basis07.row669)) (add node00113 Basis07.row675))) (add (add (add node00886 node01079) (add node00385 node01496)) (add (add node00795 node02141) (add Basis07.row688 node03031)))) (add (add (add (t Basis07.row691) (add (t Basis07.row692) Basis07.row696)) (add (add node01229 node01433) (add Basis07.row704 Basis07.row705))) (add (add (add (t Basis07.row707) node03950) (add (t Basis07.row711) (t Basis07.row712))) (add (add (t Basis07.row713) node00707) (add (t Basis07.row717) (t Basis07.row718)))))) (add (add (add (add (t Basis07.row721) (add node02133 (t Basis07.row724))) (add (add node01141 (t Basis07.row727)) (add (t Basis07.row728) node02543))) (add (add (add node01099 (t Basis07.row734)) (add node03724 node01322)) (add (add (t Basis07.row743) node02245) (add node02564 node01332)))) (add (add (add Basis07.row751 (add node01473 Basis07.row756)) (add (add (t Basis07.row757) node02246) (add node00841 node02208))) (add (add (add node02087 (t Basis07.row769)) (add (t Basis07.row770) Basis07.row772)) (add (add (t Basis07.row772) node03609) (add (t Basis07.row777) node02638)))))) (add (add (add (add (add node03231 (add node02122 node02568)) (add (add (t Basis07.row788) (t Basis07.row789)) (add node02015 (t Basis07.row794)))) (add (add (add Basis07.row795 node01589) (add (t Basis07.row798) Basis07.row800)) (add (add Basis07.row801 Basis07.row802) (add Basis07.row803 node00633)))) (add (add (add node03621 (add (t Basis07.row810) node02308)) (add (add node00218 node01687) (add Basis07.row818 (t Basis07.row819)))) (add (add (add Basis07.row820 Basis07.row822) (add node02721 Basis07.row826)) (add (add (t Basis07.row828) node02126) (add (t Basis07.row832) (t Basis07.row833)))))) (add (add (add (add node00533 (add (t Basis07.row836) Basis07.row837)) (add (add node04325 node02261) (add node00104 (t Basis07.row849)))) (add (add (add node00189 (t Basis07.row854)) (add node01221 node02948)) (add (add node00473 Basis07.row860) (add Basis07.row861 node00876)))) (add (add (add (add (t Basis07.row863) node01855) (add node01796 node02389)) (add (add node01264 (t Basis07.row877)) (add node02595 Basis07.row881))) (add (add (add node03409 Basis07.row884) (add (t Basis07.row885) node01249)) (add (add node01193 node01737) (add (t Basis07.row892) node01674)))))))))

private theorem row209 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 209 (0, 0)) ((rowsAt 10).getD 209 (0, 0)) := by
  apply of_certificate witness209
  · decide +kernel
  · decide +kernel

private noncomputable def witness210 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add node00947 (add Basis07.row003 node02959)) (add (add node02762 (t Basis07.row009)) (add Basis07.row010 node01144))) (add (add (add node00591 node00822) (add node00190 node00807)) (add (add (t Basis07.row017) node00842) (add node02533 node00534)))) (add (add (add (add node02222 node04388) (add node02175 (t Basis07.row032))) (add (add node00266 (t Basis07.row036)) (add (t Basis07.row038) (t Basis07.row040)))) (add (add (add Basis07.row041 Basis07.row042) (add (t Basis07.row044) node03493)) (add (add node00026 node00357) (add node01874 node01747))))) (add (add (add (add (t Basis07.row054) (add node00072 (t Basis07.row058))) (add (add (t Basis07.row059) (t Basis07.row060)) (add Basis07.row063 (t Basis07.row064)))) (add (add (add (t Basis07.row065) node00001) (add node01513 (t Basis07.row070))) (add (add Basis07.row071 Basis07.row073) (add (t Basis07.row073) (t Basis07.row074))))) (add (add (add (add Basis07.row076 node02572) (add node01104 Basis07.row081)) (add (add node01791 Basis07.row086) (add node02042 node01021))) (add (add (add node01405 node01042) (add node01986 node02478)) (add (add node01946 node02822) (add node00592 node01819)))))) (add (add (add (add (add (t Basis07.row109) (add (t Basis07.row112) Basis07.row113)) (add (add Basis07.row114 Basis07.row116) (add node03622 Basis07.row121))) (add (add (add Basis07.row123 (t Basis07.row123)) (add node01124 node01597)) (add (add node00771 (t Basis07.row129)) (add node01230 Basis07.row134)))) (add (add (add (add (t Basis07.row135) node00514) (add node00497 (t Basis07.row140))) (add (add (t Basis07.row141) node02479) (add node01639 Basis07.row147))) (add (add (add Basis07.row148 (t Basis07.row148)) (add Basis07.row149 Basis07.row150)) (add (add (t Basis07.row150) Basis07.row152) (add Basis07.row153 (t Basis07.row154)))))) (add (add (add (add Basis07.row155 (add node01949 Basis07.row158)) (add (add (t Basis07.row158) Basis07.row160) (add node00092 node04125))) (add (add (add node00571 (t Basis07.row170)) (add node01409 (t Basis07.row173))) (add (add (t Basis07.row174) node03705) (add node02669 Basis07.row180)))) (add (add (add (add Basis07.row181 Basis07.row182) (add Basis07.row183 node01598)) (add (add node03175 node00416) (add node01437 (t Basis07.row194)))) (add (add (add Basis07.row195 Basis07.row196) (add (t Basis07.row198) node01136)) (add (add (t Basis07.row201) Basis07.row204) (add node02461 (t Basis07.row208)))))))) (add (add (add (add (add (add node01749 (add node01621 node03018)) (add (add Basis07.row216 Basis07.row217) (add (t Basis07.row217) (t Basis07.row218)))) (add (add (add (t Basis07.row219) node00774) (add node04052 node02929)) (add (add node02517 node00224) (add node01751 node03964)))) (add (add (add (add (t Basis07.row235) node01449) (add (t Basis07.row239) Basis07.row240)) (add (add Basis07.row242 node00499) (add (t Basis07.row244) node00783))) (add (add (add node02373 node03625) (add (t Basis07.row253) Basis07.row254)) (add (add node03980 (t Basis07.row257)) (add node03572 node01518))))) (add (add (add (add node01892 (add node03254 (t Basis07.row268))) (add (add node00851 node00952) (add node02447 (t Basis07.row277)))) (add (add (add node01804 node03372) (add node01011 (t Basis07.row283))) (add (add node03588 (t Basis07.row287)) (add Basis07.row290 (t Basis07.row291))))) (add (add (add (add Basis07.row293 (t Basis07.row293)) (add node01592 node04274)) (add (add Basis07.row299 (t Basis07.row301)) (add (t Basis07.row302) (t Basis07.row303)))) (add (add (add Basis07.row305 Basis07.row307) (add Basis07.row308 node01954)) (add (add node00290 node01091) (add Basis07.row313 node04305)))))) (add (add (add (add (add (t Basis07.row318) (add Basis07.row319 node00172)) (add (add (t Basis07.row322) node03760) (add node01732 node02148))) (add (add (add Basis07.row329 (t Basis07.row330)) (add Basis07.row333 Basis07.row334)) (add (add node00152 node01827) (add node02098 node02735)))) (add (add (add (add node01309 Basis07.row347) (add Basis07.row348 Basis07.row349)) (add (add node04132 node03155) (add node00077 Basis07.row360))) (add (add (add (t Basis07.row362) node00122) (add (t Basis07.row365) Basis07.row369)) (add (add (t Basis07.row370) (t Basis07.row371)) (add node01479 (t Basis07.row374)))))) (add (add (add (add Basis07.row376 (add Basis07.row377 (t Basis07.row378))) (add (add Basis07.row381 node00336) (add (t Basis07.row383) Basis07.row385))) (add (add (add (t Basis07.row386) (t Basis07.row387)) (add (t Basis07.row388) node00483)) (add (add node01277 (t Basis07.row393)) (add node01098 node03575)))) (add (add (add (add node02821 (t Basis07.row403)) (add (t Basis07.row406) (t Basis07.row407))) (add (add node01715 Basis07.row412) (add node00564 node01292))) (add (add (add Basis07.row418 node03272) (add node00565 node04135)) (add (add (t Basis07.row429) (t Basis07.row431)) (add Basis07.row433 (t Basis07.row434))))))))) (add (add (add (add (add (add (add node03527 (add node01200 (t Basis07.row439))) (add (add node01344 node03668) (add Basis07.row446 Basis07.row447))) (add (add (add (t Basis07.row449) node02289) (add Basis07.row452 node02592)) (add (add Basis07.row457 Basis07.row458) (add (t Basis07.row458) Basis07.row459)))) (add (add (add (add node01881 node00523) (add node03113 Basis07.row468)) (add (add node00614 (t Basis07.row472)) (add (t Basis07.row473) node01797))) (add (add (add (t Basis07.row477) node00341) (add node02710 node00791)) (add (add node01107 Basis07.row486) (add (t Basis07.row486) node04027))))) (add (add (add (add node03452 (add node01870 node01717)) (add (add Basis07.row496 node02170) (add (t Basis07.row499) node00642))) (add (add (add (t Basis07.row502) node02990) (add node02190 node01420)) (add (add Basis07.row510 node01485) (add node00174 node02350)))) (add (add (add (add (t Basis07.row516) Basis07.row518) (add (t Basis07.row519) Basis07.row520)) (add (add node00897 node02991) (add Basis07.row527 (t Basis07.row528)))) (add (add (add node02876 node04254) (add node01774 node01232)) (add (add node03689 (t Basis07.row543)) (add Basis07.row546 (t Basis07.row547))))))) (add (add (add (add (add (t Basis07.row548) (add node00165 Basis07.row553)) (add (add node01289 Basis07.row556) (add node02163 (t Basis07.row559)))) (add (add (add node02940 (t Basis07.row565)) (add node03307 (t Basis07.row569))) (add (add Basis07.row570 node02496) (add node03180 node01568)))) (add (add (add (add (t Basis07.row579) node00617) (add (t Basis07.row583) Basis07.row586)) (add (add node00024 (t Basis07.row589)) (add (t Basis07.row590) Basis07.row592))) (add (add (add node00872 (t Basis07.row595)) (add Basis07.row597 (t Basis07.row597))) (add (add (t Basis07.row599) Basis07.row602) (add Basis07.row603 (t Basis07.row604)))))) (add (add (add (add node01325 (add node01031 Basis07.row611)) (add (add (t Basis07.row612) node01240) (add Basis07.row617 (t Basis07.row618)))) (add (add (add Basis07.row620 node03232) (add node02629 (t Basis07.row626))) (add (add Basis07.row627 (t Basis07.row628)) (add (t Basis07.row629) node02765)))) (add (add (add (add node04032 (t Basis07.row636)) (add Basis07.row637 Basis07.row638)) (add (add node00345 node00406) (add node01032 node01528))) (add (add (add node00088 node03094) (add node03243 node01916)) (add (add node01018 node02196) (add Basis07.row665 Basis07.row666))))))) (add (add (add (add (add (add node01964 (add node03163 (t Basis07.row673))) (add (add Basis07.row674 Basis07.row675) (add (t Basis07.row676) Basis07.row677))) (add (add (add (t Basis07.row678) node00936) (add Basis07.row682 node03393)) (add (add node02140 node04147) (add Basis07.row691 node04164)))) (add (add (add (add node00215 node01489) (add node00434 node04148)) (add (add (t Basis07.row702) node02462) (add Basis07.row706 node03951))) (add (add (add Basis07.row712 node00619) (add (t Basis07.row716) (t Basis07.row717))) (add (add node02845 Basis07.row720) (add (t Basis07.row720) (t Basis07.row722)))))) (add (add (add (add (t Basis07.row724) (add node00233 node02921)) (add (add node00278 node01186) (add node00556 (t Basis07.row739)))) (add (add (add Basis07.row741 node04374) (add (t Basis07.row745) node02579)) (add (add node00296 Basis07.row751) (add Basis07.row752 Basis07.row753)))) (add (add (add (add node00546 (t Basis07.row756)) (add Basis07.row757 (t Basis07.row759))) (add (add node01180 (t Basis07.row762)) (add node00387 Basis07.row770))) (add (add (add (t Basis07.row771) node04278) (add (t Basis07.row776) node00004)) (add (add node02139 Basis07.row781) (add Basis07.row784 (t Basis07.row785))))))) (add (add (add (add (add Basis07.row786 (add node01248 Basis07.row790)) (add (add Basis07.row791 node02703) (add node02341 node01404))) (add (add (add (t Basis07.row798) Basis07.row799) (add Basis07.row800 (t Basis07.row802))) (add (add (t Basis07.row803) Basis07.row804) (add Basis07.row805 Basis07.row806)))) (add (add (add (add Basis07.row807 node01400) (add (t Basis07.row811) (t Basis07.row812))) (add (add node00218 node01800) (add Basis07.row818 node03936))) (add (add (add (t Basis07.row821) node03464) (add node04387 node02529)) (add (add Basis07.row831 node03239) (add Basis07.row835 Basis07.row836))))) (add (add (add (add (add (t Basis07.row836) (t Basis07.row839)) (add Basis07.row840 node01616)) (add (add Basis07.row843 Basis07.row845) (add Basis07.row846 node02952))) (add (add (add (t Basis07.row849) node02018) (add (t Basis07.row853) (t Basis07.row854))) (add (add (t Basis07.row855) Basis07.row856) (add node03047 Basis07.row860)))) (add (add (add (add Basis07.row862 node03127) (add Basis07.row865 node01378)) (add (add Basis07.row868 Basis07.row870) (add node02389 node00331))) (add (add (add node03233 (t Basis07.row881)) (add node03410 Basis07.row887)) (add (add Basis07.row888 node01737) (add node02646 Basis07.row894)))))))))

private theorem row210 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 210 (0, 0)) ((rowsAt 10).getD 210 (0, 0)) := by
  apply of_certificate witness210
  · decide +kernel
  · decide +kernel

private noncomputable def witness211 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row058

private theorem row211 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 211 (0, 0)) ((rowsAt 10).getD 211 (0, 0)) := by
  apply of_certificate witness211
  · decide +kernel
  · decide +kernel

private noncomputable def witness212 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add Basis07.row000 (add node02930 node02805)) (add (add (t Basis07.row005) (t Basis07.row007)) (add node03808 node01940))) (add (add node02680 (add node01206 Basis07.row018)) (add (add node02798 (t Basis07.row021)) (add Basis07.row022 node02273)))) (add (add (add node00282 (add (t Basis07.row028) (t Basis07.row030))) (add (add Basis07.row032 node02475) (add (t Basis07.row036) node04327))) (add (add (add node00220 node01450) (add Basis07.row047 node04391)) (add (add node00475 (t Basis07.row052)) (add Basis07.row053 Basis07.row054))))) (add (add (add (add node03510 (add (t Basis07.row057) (t Basis07.row058))) (add (add node03511 (t Basis07.row062)) (add Basis07.row063 (t Basis07.row064)))) (add (add (add node01887 node01856) (add node00106 Basis07.row070)) (add (add node01039 node01008) (add Basis07.row077 Basis07.row079)))) (add (add (add (t Basis07.row079) (add node01736 node00856)) (add (add (t Basis07.row087) (t Basis07.row091)) (add (t Basis07.row092) node03081))) (add (add (add node01307 Basis07.row098) (add (t Basis07.row098) (t Basis07.row099))) (add (add (t Basis07.row101) node01760) (add node02587 Basis07.row108)))))) (add (add (add (add (add node01394 (add Basis07.row111 node00362)) (add (add Basis07.row116 Basis07.row117) (add node02443 node02317))) (add (add node02732 (add node00945 node01880)) (add (add node00649 node03295) (add node03367 (t Basis07.row136))))) (add (add (add Basis07.row140 (add node01820 node02226)) (add (add (t Basis07.row144) (t Basis07.row145)) (add node00676 (t Basis07.row149)))) (add (add (add node02095 node02355) (add Basis07.row154 node01647)) (add (add node00976 (t Basis07.row159)) (add node03909 (t Basis07.row162)))))) (add (add (add (add (t Basis07.row164) (add node01226 node00380)) (add (add node04206 node02676) (add Basis07.row174 (t Basis07.row176)))) (add (add (add (t Basis07.row177) node01283) (add (t Basis07.row181) node02047)) (add (add Basis07.row184 (t Basis07.row186)) (add node00802 node01705)))) (add (add (add node01152 (add node01650 node00240)) (add (add Basis07.row197 Basis07.row198) (add Basis07.row202 node01387))) (add (add (add Basis07.row204 node00223) (add node00677 node01706)) (add (add (t Basis07.row213) (t Basis07.row215)) (add (t Basis07.row216) (t Basis07.row217)))))))) (add (add (add (add (add (add (t Basis07.row219) (add node01388 Basis07.row223)) (add (add Basis07.row224 node03491) (add node04403 node01261))) (add (add (t Basis07.row232) (add Basis07.row233 node00395)) (add (add node02358 node00095) (add Basis07.row241 (t Basis07.row241))))) (add (add (add (t Basis07.row245) (add node00783 node00171)) (add (add node02696 (t Basis07.row251)) (add Basis07.row252 (t Basis07.row255)))) (add (add (add node01154 node02890) (add Basis07.row263 node02570)) (add (add (t Basis07.row266) node00994) (add node01794 node00920))))) (add (add (add (add Basis07.row273 (add (t Basis07.row274) Basis07.row275)) (add (add (t Basis07.row276) node04303) (add Basis07.row281 node03500))) (add (add (add Basis07.row286 node02036) (add (t Basis07.row290) node00311)) (add (add node01046 node00021) (add node00858 Basis07.row299)))) (add (add (add node01288 (add node02401 node00502)) (add (add node00225 Basis07.row310) (add node00443 node00119))) (add (add (add node01047 Basis07.row320) (add node04177 (t Basis07.row326))) (add (add node03106 node01125) (add node02187 node02983)))))) (add (add (add (add (add Basis07.row338 (add node02098 Basis07.row343)) (add (add node00082 node00784) (add node01829 node00762))) (add (add (add (t Basis07.row351) Basis07.row352) (add (t Basis07.row352) Basis07.row357)) (add (add Basis07.row360 node00612) (add (t Basis07.row363) node03592)))) (add (add (add node00895 (add node01561 node00208)) (add (add node03594 Basis07.row377) (add (t Basis07.row378) Basis07.row379))) (add (add (add (t Basis07.row380) node02560) (add node00599 node00981)) (add (add Basis07.row389 node00483) (add Basis07.row393 node01958))))) (add (add (add (add (t Basis07.row397) (add node01132 Basis07.row400)) (add (add node03892 Basis07.row404) (add Basis07.row405 (t Basis07.row405)))) (add (add (add node00705 node01715) (add node03132 (t Basis07.row412))) (add (add node03157 node00721) (add node03869 (t Basis07.row421))))) (add (add (add (t Basis07.row423) (add node01114 node01455)) (add (add node02000 (t Basis07.row431)) (add node02616 node03378))) (add (add (add node00781 node01742) (add node03425 node00653)) (add (add Basis07.row449 node00828) (add node02960 (t Basis07.row452))))))))) (add (add (add (add (add (add (add node02491 (add (t Basis07.row455) node01564)) (add (add node01960 (t Basis07.row463)) (add node00524 node02473))) (add (add node01194 (add (t Basis07.row470) node01209)) (add (add (t Basis07.row473) (t Basis07.row474)) (add Basis07.row478 Basis07.row479)))) (add (add (add (t Basis07.row479) (add node02926 node00553)) (add (add node04329 Basis07.row489) (add (t Basis07.row489) Basis07.row492))) (add (add (add Basis07.row493 Basis07.row498) (add node01930 Basis07.row502)) (add (add node02334 Basis07.row505) (add node01276 Basis07.row508))))) (add (add (add (add node02521 (add (t Basis07.row514) (t Basis07.row515))) (add (add node03962 node00085) (add node01356 node03661))) (add (add (add Basis07.row525 node00849) (add Basis07.row528 (t Basis07.row530))) (add (add node02109 node01355) (add node02191 (t Basis07.row536))))) (add (add (add node01312 (add (t Basis07.row540) (t Basis07.row542))) (add (add node02671 (t Basis07.row546)) (add (t Basis07.row548) Basis07.row549))) (add (add (add (t Basis07.row551) node00450) (add node00031 node00933)) (add (add node01271 node01961) (add (t Basis07.row562) node01298)))))) (add (add (add (add (add node00432 (add node03773 Basis07.row569)) (add (add Basis07.row571 Basis07.row572) (add node01487 node03455))) (add (add (add node02319 node01608) (add node00321 node02400)) (add (add (t Basis07.row586) (t Basis07.row587)) (add Basis07.row588 Basis07.row589)))) (add (add (add (t Basis07.row589) (add Basis07.row592 node00810)) (add (add Basis07.row596 (t Basis07.row598)) (add Basis07.row599 Basis07.row600))) (add (add (add node01189 node00722) (add node01269 node02193)) (add (add node02258 Basis07.row612) (add (t Basis07.row612) (t Basis07.row613)))))) (add (add (add (add node01240 (add node00159 node02180)) (add (add (t Basis07.row620) Basis07.row622) (add (t Basis07.row624) Basis07.row625))) (add (add (add node02206 node04171) (add node02010 node01117)) (add (add node01526 (t Basis07.row639)) (add Basis07.row640 node00040)))) (add (add (add node01798 (add Basis07.row647 node00923)) (add (add node00745 node03877) (add node04230 (t Basis07.row658)))) (add (add (add node01018 node02336) (add node00245 (t Basis07.row667))) (add (add node01345 node02917) (add (t Basis07.row672) (t Basis07.row673)))))))) (add (add (add (add (add (add (t Basis07.row674) (add Basis07.row675 (t Basis07.row676))) (add (add node00811 node03477) (add (t Basis07.row682) node00631))) (add (add (t Basis07.row687) (add (t Basis07.row688) Basis07.row689)) (add (add (t Basis07.row690) Basis07.row693) (add node03008 Basis07.row697)))) (add (add (add Basis07.row698 (add node03317 node03398)) (add (add Basis07.row706 Basis07.row708) (add node01779 node01864))) (add (add (add node00006 node01490) (add node00142 node01299)) (add (add Basis07.row723 node04285) (add Basis07.row726 node00325))))) (add (add (add (add node00620 (add node01849 node00887)) (add (add Basis07.row738 node04021) (add (t Basis07.row744) (t Basis07.row746)))) (add (add (add (t Basis07.row749) (t Basis07.row750)) (add (t Basis07.row751) (t Basis07.row752))) (add (add Basis07.row755 node00530) (add (t Basis07.row758) (t Basis07.row759))))) (add (add (add Basis07.row760 (add node00797 Basis07.row763)) (add (add Basis07.row764 node02087) (add Basis07.row768 Basis07.row770))) (add (add (add (t Basis07.row772) (t Basis07.row774)) (add Basis07.row776 Basis07.row778)) (add (add node00409 Basis07.row782) (add node01912 Basis07.row786)))))) (add (add (add (add (add (t Basis07.row787) (add Basis07.row791 node02703)) (add (add node02594 node00925) (add node00580 node00701))) (add (add (add node00621 Basis07.row806) (add Basis07.row807 node03124)) (add (add (t Basis07.row811) (t Basis07.row812)) (add Basis07.row814 (t Basis07.row814))))) (add (add (add node01531 (add node00659 node00547)) (add (add (t Basis07.row821) (t Basis07.row822)) (add (t Basis07.row824) (t Basis07.row826)))) (add (add (add Basis07.row828 node02065) (add (t Basis07.row830) (t Basis07.row831))) (add (add Basis07.row832 node00533) (add node03283 Basis07.row838))))) (add (add (add (add Basis07.row839 (add Basis07.row841 node00863)) (add (add node02214 node03704) (add node00356 Basis07.row851))) (add (add (add Basis07.row854 node02864) (add node01512 node01227)) (add (add node01020 Basis07.row866) (add (t Basis07.row867) node01003)))) (add (add (add node01532 (add node00646 node01264)) (add (add node03474 (t Basis07.row878)) (add node03074 Basis07.row882))) (add (add (add (t Basis07.row883) Basis07.row885) (add (t Basis07.row885) node00719)) (add (add node01193 node00146) (add (t Basis07.row894) Basis07.row895)))))))))

private theorem row212 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 212 (0, 0)) ((rowsAt 10).getD 212 (0, 0)) := by
  apply of_certificate witness212
  · decide +kernel
  · decide +kernel

private noncomputable def witness213 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row505

private theorem row213 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 213 (0, 0)) ((rowsAt 10).getD 213 (0, 0)) := by
  apply of_certificate witness213
  · decide +kernel
  · decide +kernel

private noncomputable def witness214 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add node01148 (add node00132 node02257)) (add (add node03501 (t Basis07.row009)) (add (t Basis07.row010) Basis07.row014))) (add (add node02680 (add node00807 node02514)) (add (add node01385 Basis07.row023) (add Basis07.row024 node03618)))) (add (add (add (t Basis07.row030) (add (t Basis07.row031) Basis07.row032)) (add (add node00090 Basis07.row039) (add node00220 (t Basis07.row041)))) (add (add (add (t Basis07.row042) node02357) (add (t Basis07.row045) Basis07.row046)) (add (add node00026 node02079) (add (t Basis07.row053) node00510))))) (add (add (add (add node02792 (add node01701 (t Basis07.row059))) (add (add node02712 (t Basis07.row064)) (add Basis07.row065 Basis07.row066))) (add (add (add node00661 (t Basis07.row069)) (add (t Basis07.row070) Basis07.row071)) (add (add Basis07.row072 node04394) (add node03904 node02274)))) (add (add (add Basis07.row083 (add Basis07.row084 node03745)) (add (add node00476 node01021) (add node01406 Basis07.row095))) (add (add (add node01986 Basis07.row099) (add Basis07.row101 (t Basis07.row101))) (add (add node00496 node00044) (add (t Basis07.row106) node00147)))))) (add (add (add (add (add node01435 (add node03733 (t Basis07.row114))) (add (add node00286 node00297) (add (t Basis07.row119) (t Basis07.row121)))) (add (add (add node01043 node01124) (add (t Basis07.row125) (t Basis07.row126))) (add (add node01550 node02847) (add Basis07.row133 Basis07.row134)))) (add (add (add node02935 (add Basis07.row138 node01317)) (add (add node02176 Basis07.row143) (add Basis07.row151 Basis07.row152))) (add (add (add Basis07.row153 (t Basis07.row154)) (add Basis07.row156 node03054)) (add (add (t Basis07.row161) node02739) (add Basis07.row165 (t Basis07.row165)))))) (add (add (add (add node02370 (add Basis07.row170 (t Basis07.row172))) (add (add Basis07.row175 (t Basis07.row175)) (add (t Basis07.row177) Basis07.row179))) (add (add (add node00239 node00181) (add node01598 node04283)) (add (add Basis07.row190 (t Basis07.row191)) (add node00271 node02136)))) (add (add (add Basis07.row195 (add node01950 Basis07.row201)) (add (add Basis07.row204 node02461) (add (t Basis07.row207) node01633))) (add (add (add node00677 node02977) (add (t Basis07.row214) node04454)) (add (add node00517 node00774) (add node02641 Basis07.row224))))))) (add (add (add (add (add (add node03278 (add Basis07.row228 (t Basis07.row229))) (add (add node01555 node00289) (add node02027 (t Basis07.row241)))) (add (add (add (t Basis07.row242) Basis07.row243) (add (t Basis07.row247) (t Basis07.row250))) (add (add Basis07.row251 node01996) (add Basis07.row254 Basis07.row258)))) (add (add (add node04023 (add Basis07.row263 (t Basis07.row263))) (add (add node03623 (t Basis07.row267)) (add Basis07.row269 (t Basis07.row269)))) (add (add (add node03428 (t Basis07.row273)) (add Basis07.row274 (t Basis07.row275))) (add (add (t Basis07.row276) node04010) (add node01990 Basis07.row282))))) (add (add (add (add node00596 (add node00894 node00540)) (add (add node02036 node01895) (add node01537 node01592))) (add (add (add node02229 Basis07.row301) (add Basis07.row303 node02831)) (add (add node02285 node00047) (add Basis07.row311 node03560)))) (add (add (add (t Basis07.row314) (add Basis07.row315 (t Basis07.row318))) (add (add node00798 node03821) (add (t Basis07.row323) (t Basis07.row324)))) (add (add (add node02697 node01213) (add node00460 node00883)) (add (add node00906 Basis07.row333) (add Basis07.row334 node00120)))))) (add (add (add (add (add (t Basis07.row338) (add (t Basis07.row339) Basis07.row342)) (add (add node00082 node01177) (add node00302 node00109))) (add (add (add node01246 (t Basis07.row354)) (add node02411 node00077)) (add (add (t Basis07.row358) node00844) (add node04215 (t Basis07.row365))))) (add (add (add Basis07.row368 (add node02262 node00335)) (add (add (t Basis07.row374) Basis07.row375) (add Basis07.row376 node03139))) (add (add (add Basis07.row381 (t Basis07.row381)) (add (t Basis07.row382) node00049)) (add (add node00461 (t Basis07.row390)) (add node01545 node01126))))) (add (add (add (add Basis07.row396 (add (t Basis07.row396) node03575)) (add (add node00720 node00630) (add node01714 (t Basis07.row408)))) (add (add (add (t Basis07.row410) Basis07.row413) (add Basis07.row414 Basis07.row415)) (add (add (t Basis07.row417) node03438) (add node01510 node02424)))) (add (add (add node01771 (add (t Basis07.row428) node04410)) (add (add (t Basis07.row432) node02835) (add node03204 (t Basis07.row441)))) (add (add (add node03668 Basis07.row446) (add node02508 Basis07.row454)) (add (add (t Basis07.row454) node00315) (add node01564 (t Basis07.row461))))))))) (add (add (add (add (add (add (add node01508 (add node03845 node01359)) (add (add (t Basis07.row469) Basis07.row473) (add Basis07.row474 node00997))) (add (add node00317 (add (t Basis07.row482) node01235)) (add (add node00553 node00155) (add Basis07.row489 node03206)))) (add (add (add node04257 (add (t Basis07.row495) Basis07.row497)) (add (add node00850 Basis07.row500) (add (t Basis07.row502) node02334))) (add (add (add (t Basis07.row505) Basis07.row506) (add node01693 (t Basis07.row513))) (add (add node03304 node01164) (add node00505 (t Basis07.row519)))))) (add (add (add (add node02155 (add node01523 Basis07.row526)) (add (add node01802 (t Basis07.row530)) (add (t Basis07.row532) node04087))) (add (add (add node00431 node01312) (add (t Basis07.row540) node03849)) (add (add Basis07.row543 node04139) (add node00932 Basis07.row550)))) (add (add (add Basis07.row551 (add node04142 (t Basis07.row555))) (add (add Basis07.row558 (t Basis07.row558)) (add node00934 Basis07.row561))) (add (add (add node04143 node02897) (add node03306 Basis07.row569)) (add (add node01348 node01358) (add node03211 node01457)))))) (add (add (add (add (add node01197 (add (t Basis07.row581) (t Basis07.row582))) (add (add node02528 node00197) (add Basis07.row590 Basis07.row592))) (add (add (add Basis07.row593 (t Basis07.row593)) (add Basis07.row596 Basis07.row597)) (add (add node01146 node01330) (add node00935 node02464)))) (add (add (add node01814 (add Basis07.row607 (t Basis07.row608))) (add (add (t Basis07.row610) node00965) (add Basis07.row614 node01899))) (add (add (add node01055 (t Basis07.row620)) (add (t Basis07.row621) Basis07.row622)) (add (add (t Basis07.row623) (t Basis07.row625)) (add (t Basis07.row626) node02237))))) (add (add (add (add node00900 (add Basis07.row631 node02010)) (add (add Basis07.row634 node00618) (add node01983 node00305))) (add (add (add node02195 node01095) (add node01686 (t Basis07.row646))) (add (add Basis07.row648 Basis07.row649) (add node00923 (t Basis07.row654))))) (add (add (add (t Basis07.row655) (add node04230 Basis07.row659)) (add (add node01243 Basis07.row663) (add (t Basis07.row664) Basis07.row665))) (add (add (add Basis07.row666 (t Basis07.row667)) (add (t Basis07.row669) node01123)) (add (add node00373 (t Basis07.row674)) (add node00185 node00811))))))) (add (add (add (add (add (add node01070 (add node01319 (t Basis07.row686))) (add (add node01750 node01373) (add node03488 node00408))) (add (add (add Basis07.row698 node03318) (add node02118 Basis07.row704)) (add (add node02198 node01140) (add node03951 (t Basis07.row711))))) (add (add (add (t Basis07.row712) (add Basis07.row713 Basis07.row714)) (add (add (t Basis07.row715) node01062) (add node00351 node00232))) (add (add (add node03607 node01978) (add node00278 node02159)) (add (add (t Basis07.row734) Basis07.row735) (add node00061 node00216))))) (add (add (add (add node00451 (add node01499 (t Basis07.row743))) (add (add (t Basis07.row745) (t Basis07.row746)) (add Basis07.row749 Basis07.row751))) (add (add (add Basis07.row753 node03697) (add node02964 node01669)) (add (add (t Basis07.row760) Basis07.row761) (add (t Basis07.row762) node01577)))) (add (add (add (t Basis07.row766) (add node00387 (t Basis07.row769))) (add (add node03852 node01190) (add node02167 node01613))) (add (add (add node00409 Basis07.row783) (add node02384 (t Basis07.row787))) (add (add (t Basis07.row789) node00279) (add (t Basis07.row794) (t Basis07.row795))))))) (add (add (add (add (add Basis07.row796 (add node01853 node03643)) (add (add Basis07.row801 node02359) (add Basis07.row804 Basis07.row805))) (add (add (add (t Basis07.row806) (t Basis07.row807)) (add node01001 node00329)) (add (add node00878 (t Basis07.row815)) (add (t Basis07.row817) node01109)))) (add (add (add node01143 (add node03556 node03464)) (add (add node02388 node00690) (add node00494 node00533))) (add (add (add (t Basis07.row835) node03177) (add (t Basis07.row840) node02471)) (add (add node00975 Basis07.row845) (add Basis07.row846 node02951))))) (add (add (add (add Basis07.row849 (add Basis07.row850 (t Basis07.row852))) (add (add Basis07.row853 Basis07.row854) (add Basis07.row857 (t Basis07.row857)))) (add (add (add (t Basis07.row860) (t Basis07.row861)) (add Basis07.row864 Basis07.row865)) (add (add Basis07.row867 Basis07.row869) (add node01590 Basis07.row872)))) (add (add (add Basis07.row873 (add (t Basis07.row873) (t Basis07.row875))) (add (add node04362 node03578) (add Basis07.row881 (t Basis07.row881)))) (add (add (add (t Basis07.row883) (t Basis07.row887)) (add (t Basis07.row888) Basis07.row890)) (add (add Basis07.row891 Basis07.row893) (add (t Basis07.row894) (t Basis07.row895))))))))))

private theorem row214 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 214 (0, 0)) ((rowsAt 10).getD 214 (0, 0)) := by
  apply of_certificate witness214
  · decide +kernel
  · decide +kernel

private noncomputable def witness215 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row510

private theorem row215 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 215 (0, 0)) ((rowsAt 10).getD 215 (0, 0)) := by
  apply of_certificate witness215
  · decide +kernel
  · decide +kernel

private noncomputable def witness216 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add node02678 (add (t Basis07.row003) Basis07.row004)) (add (add node02506 (t Basis07.row007)) (add node01234 node00415))) (add (add (add node00435 node01940) (add node00190 node00807)) (add (add Basis07.row020 node02782) (add node00559 (t Basis07.row027))))) (add (add (add node00712 (add node02571 (t Basis07.row035))) (add (add node00991 (t Basis07.row038)) (add Basis07.row040 Basis07.row042))) (add (add (add (t Basis07.row043) (t Basis07.row044)) (add node00026 node02211)) (add (add Basis07.row051 node01747) (add node00091 Basis07.row056))))) (add (add (add (add node01700 (add Basis07.row060 (t Basis07.row060))) (add (add Basis07.row063 (t Basis07.row064)) (add node00073 (t Basis07.row067)))) (add (add (add (t Basis07.row068) node00065) (add Basis07.row072 Basis07.row073)) (add (add node01323 node02572) (add node03829 node02722)))) (add (add (add (add node00135 node02092) (add Basis07.row089 Basis07.row090)) (add (add (t Basis07.row090) Basis07.row092) (add (t Basis07.row093) (t Basis07.row094)))) (add (add (add node02182 Basis07.row098) (add (t Basis07.row098) Basis07.row100)) (add (add Basis07.row101 Basis07.row102) (add node03741 (t Basis07.row109))))))) (add (add (add (add (add Basis07.row110 (add Basis07.row111 node02618)) (add (add (t Basis07.row116) Basis07.row117) (add (t Basis07.row117) node02681))) (add (add (add node00949 node00437) (add node02648 node02043)) (add (add (t Basis07.row130) node01584) (add node00843 node03513)))) (add (add (add (add node00028 node01948) (add (t Basis07.row141) node00713)) (add (add node01937 (t Basis07.row148)) (add node00881 Basis07.row152))) (add (add (add Basis07.row153 node01515) (add node03882 node00439)) (add (add node03909 node02327) (add Basis07.row165 Basis07.row166))))) (add (add (add (add (t Basis07.row166) (add node00045 node01649)) (add (add (t Basis07.row177) Basis07.row180) (add (t Basis07.row182) Basis07.row183))) (add (add (add Basis07.row186 node04283) (add (t Basis07.row191) (t Basis07.row192))) (add (add (t Basis07.row193) node01363) (add (t Basis07.row197) (t Basis07.row198))))) (add (add (add (add Basis07.row200 node02282) (add (t Basis07.row203) Basis07.row204)) (add (add (t Basis07.row205) (t Basis07.row206)) (add Basis07.row208 Basis07.row209))) (add (add (add (t Basis07.row209) (t Basis07.row210)) (add node02205 (t Basis07.row213))) (add (add (t Basis07.row214) node00516) (add node03103 node02553))))))) (add (add (add (add (add (add Basis07.row223 (add node00804 Basis07.row227)) (add (add node03551 (t Basis07.row229)) (add (t Basis07.row231) node02970))) (add (add (add node02185 node00678) (add Basis07.row239 Basis07.row242)) (add (add node01026 node01994) (add (t Basis07.row246) (t Basis07.row247))))) (add (add (add (add node04126 node03007) (add node02524 node01027)) (add (add (t Basis07.row258) (t Basis07.row259)) (add Basis07.row260 Basis07.row262))) (add (add (add node03623 (t Basis07.row268)) (add node04302 (t Basis07.row273))) (add (add node01121 node01028) (add Basis07.row278 Basis07.row279))))) (add (add (add (add node01990 (add Basis07.row282 node02033)) (add (add (t Basis07.row286) (t Basis07.row287)) (add node01895 node01826))) (add (add (add Basis07.row293 (t Basis07.row293)) (add node01592 (t Basis07.row297))) (add (add (t Basis07.row298) (t Basis07.row299)) (add Basis07.row300 Basis07.row302)))) (add (add (add (add Basis07.row303 Basis07.row304) (add (t Basis07.row304) node01090)) (add (add node01272 node00867) (add (t Basis07.row315) node00119))) (add (add (add Basis07.row318 (t Basis07.row318)) (add node02938 (t Basis07.row322))) (add (add (t Basis07.row324) (t Basis07.row325)) (add (t Basis07.row326) Basis07.row327)))))) (add (add (add (add (add node03148 (add Basis07.row331 (t Basis07.row331))) (add (add (t Basis07.row332) (t Basis07.row333)) (add Basis07.row334 node00980))) (add (add (add Basis07.row337 node02437) (add node02923 node01617)) (add (add node02053 node00302) (add node01218 node00244)))) (add (add (add (add node00987 (t Basis07.row355)) (add (t Basis07.row356) Basis07.row357)) (add (add node01588 node03521) (add (t Basis07.row362) node00961))) (add (add (add (t Basis07.row366) (t Basis07.row368)) (add (t Basis07.row369) Basis07.row371)) (add (add (t Basis07.row372) Basis07.row373) (add Basis07.row375 node01480))))) (add (add (add (add node03416 (add (t Basis07.row380) Basis07.row382)) (add (add (t Basis07.row382) node03286) (add node00809 node01562))) (add (add (add Basis07.row390 (t Basis07.row391)) (add Basis07.row392 node03110)) (add (add Basis07.row396 (t Basis07.row396)) (add node03203 node01711)))) (add (add (add (add node00630 node00425) (add node01713 node00574)) (add (add Basis07.row409 node00227) (add node00564 node02413))) (add (add (add node01576 node00565) (add (t Basis07.row423) node03844)) (add (add Basis07.row427 Basis07.row428) (add node04091 Basis07.row431)))))))) (add (add (add (add (add (add (add (t Basis07.row432) (add Basis07.row433 Basis07.row435)) (add (add node03337 node01200) (add (t Basis07.row440) node04042))) (add (add (add node02575 (t Basis07.row448)) (add node03060 Basis07.row452)) (add (add (t Basis07.row452) (t Basis07.row453)) (add (t Basis07.row454) Basis07.row458)))) (add (add (add (add (t Basis07.row458) (t Basis07.row459)) (add node01390 (t Basis07.row462))) (add (add Basis07.row463 Basis07.row464) (add (t Basis07.row465) Basis07.row468))) (add (add (add node01093 node00485) (add node01195 Basis07.row474)) (add (add node01716 node01591) (add (t Basis07.row479) node04384))))) (add (add (add (add Basis07.row484 (add Basis07.row486 Basis07.row487)) (add (add node03422 node01870) (add node01293 Basis07.row497))) (add (add (add (t Basis07.row497) (t Basis07.row500)) (add (t Basis07.row501) node00759)) (add (add (t Basis07.row505) node01276) (add Basis07.row508 Basis07.row511)))) (add (add (add (add node02521 node03304) (add (t Basis07.row516) node00505)) (add (add (t Basis07.row519) Basis07.row520) (add Basis07.row522 node00897))) (add (add (add node00789 (t Basis07.row526)) (add node01872 (t Basis07.row530))) (add (add node02156 Basis07.row537) (add Basis07.row538 Basis07.row540)))))) (add (add (add (add (add node00998 (add Basis07.row543 node00175)) (add (add node03770 node00943) (add node04141 (t Basis07.row553)))) (add (add (add Basis07.row554 Basis07.row555) (add node00933 node02112)) (add (add node00589 node03693) (add node00732 node00228)))) (add (add (add (add (t Basis07.row569) Basis07.row570) (add node01734 Basis07.row574)) (add (add node03774 node01457) (add Basis07.row580 node01924))) (add (add (add node04145 node00343) (add node02008 Basis07.row589)) (add (add (t Basis07.row590) Basis07.row592) (add node02363 node01116))))) (add (add (add (add Basis07.row598 (add node01803 node04486)) (add (add (t Basis07.row603) node01814) (add node01374 Basis07.row609))) (add (add (add node00033 Basis07.row612) (add (t Basis07.row614) Basis07.row616)) (add (add node02180 (t Basis07.row621)) (add node01263 Basis07.row629)))) (add (add (add (add (t Basis07.row630) node01879) (add node00384 node01117)) (add (add (t Basis07.row637) node01685) (add node03391 (t Basis07.row642)))) (add (add (add node00914 node01799) (add Basis07.row647 node00974)) (add (add node01812 node00577) (add Basis07.row657 Basis07.row659))))))) (add (add (add (add (add (add Basis07.row660 (add Basis07.row661 (t Basis07.row662))) (add (add Basis07.row665 Basis07.row667) (add node03069 Basis07.row671))) (add (add (add (t Basis07.row673) node01626) (add node00886 node00213)) (add (add (t Basis07.row679) node02157) (add (t Basis07.row685) node00053)))) (add (add (add (add node00491 node00214) (add Basis07.row694 (t Basis07.row694))) (add (add Basis07.row695 node01423) (add (t Basis07.row698) Basis07.row699))) (add (add (add Basis07.row700 Basis07.row703) (add (t Basis07.row707) node00937)) (add (add node00293 node01902) (add (t Basis07.row715) (t Basis07.row716)))))) (add (add (add (add Basis07.row717 (add node02381 node00386)) (add (add Basis07.row723 (t Basis07.row723)) (add node03013 node02776))) (add (add (add (t Basis07.row732) node01849) (add (t Basis07.row737) node00938)) (add (add node01499 Basis07.row743) (add (t Basis07.row743) (t Basis07.row745))))) (add (add (add (add node01781 node01977) (add node02012 (t Basis07.row754))) (add (add (t Basis07.row755) node00767) (add node03217 node04355))) (add (add (add Basis07.row765 Basis07.row766) (add node02467 node01255)) (add (add Basis07.row771 node00328) (add node00785 (t Basis07.row778))))))) (add (add (add (add (add node03574 (add Basis07.row783 node01300)) (add (add node00390 node00063) (add node02173 node02340))) (add (add (add (t Basis07.row794) Basis07.row795) (add node02526 (t Basis07.row798))) (add (add node02894 node03933) (add Basis07.row804 Basis07.row805)))) (add (add (add (add node03784 Basis07.row809) (add (t Basis07.row809) node02645)) (add (add node02810 (t Basis07.row817)) (add (t Basis07.row819) (t Basis07.row820)))) (add (add (add node00548 node03190) (add node02786 Basis07.row833)) (add (add Basis07.row835 Basis07.row836) (add node01006 node04237))))) (add (add (add (add Basis07.row841 (add node03789 (t Basis07.row845))) (add (add node03857 Basis07.row849) (add Basis07.row853 node00675))) (add (add (add node00624 (t Basis07.row858)) (add Basis07.row859 (t Basis07.row860))) (add (add Basis07.row862 node02882) (add Basis07.row866 node03610)))) (add (add (add (add Basis07.row871 Basis07.row872) (add (t Basis07.row872) node02460)) (add (add Basis07.row876 (t Basis07.row876)) (add (t Basis07.row877) (t Basis07.row880)))) (add (add (add node00248 node03090) (add node00959 Basis07.row889)) (add (add (t Basis07.row889) node01738) (add (t Basis07.row892) node00669)))))))))

private theorem row216 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 216 (0, 0)) ((rowsAt 10).getD 216 (0, 0)) := by
  apply of_certificate witness216
  · decide +kernel
  · decide +kernel

private noncomputable def witness217 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add (t Basis07.row000) (add (t Basis07.row003) node04293)) (add (add Basis07.row008 node03808) (add node03149 node00822))) (add (add (add node00190 node00807) (add Basis07.row019 Basis07.row020)) (add (add (t Basis07.row020) node02273) (add node00282 Basis07.row028)))) (add (add (add (t Basis07.row028) (add Basis07.row030 node00179)) (add (add node01398 node00283) (add node01497 node01120))) (add (add (add node00607 node01476) (add (t Basis07.row049) node02665)) (add (add node02792 (t Basis07.row057)) (add node03862 node00703))))) (add (add (add (add (t Basis07.row064) (add Basis07.row067 node00106)) (add (add Basis07.row070 Basis07.row073) (add (t Basis07.row074) Basis07.row075))) (add (add (add node01923 Basis07.row079) (add Basis07.row080 Basis07.row081)) (add (add Basis07.row082 Basis07.row083) (add Basis07.row084 node02850)))) (add (add (add (t Basis07.row088) (add (t Basis07.row090) node02583)) (add (add node01042 node00009) (add node02212 (t Basis07.row099)))) (add (add (add Basis07.row101 (t Basis07.row101)) (add node02406 node00044)) (add (add Basis07.row107 Basis07.row110) (add (t Basis07.row111) Basis07.row112)))))) (add (add (add (add (add node00478 (add node01683 node03195)) (add (add Basis07.row119 (t Basis07.row119)) (add Basis07.row120 node00840))) (add (add (add Basis07.row125 Basis07.row126) (add (t Basis07.row128) node03672)) (add (add Basis07.row132 (t Basis07.row135)) (add node04270 (t Basis07.row138))))) (add (add (add (t Basis07.row140) (add (t Basis07.row142) node02806)) (add (add node02084 (t Basis07.row149)) (add node02095 node02355))) (add (add (add Basis07.row154 node01647) (add (t Basis07.row157) Basis07.row158)) (add (add (t Basis07.row159) node01890) (add node01165 node03831))))) (add (add (add (add (t Basis07.row168) (add node00045 (t Basis07.row172))) (add (add Basis07.row175 node00968) (add (t Basis07.row181) node04049))) (add (add (add node01692 (t Basis07.row188)) (add node01152 node02589)) (add (add Basis07.row195 Basis07.row199) (add node02936 node02830)))) (add (add (add node01599 (add node03710 (t Basis07.row209))) (add (add (t Basis07.row210) Basis07.row212) (add (t Basis07.row212) Basis07.row214))) (add (add (add (t Basis07.row216) node01824) (add Basis07.row224 node02898)) (add (add node00241 Basis07.row230) (add node01805 (t Basis07.row233)))))))) (add (add (add (add (add (add (t Basis07.row234) (add node01869 (t Basis07.row237))) (add (add (t Basis07.row240) (t Basis07.row241)) (add Basis07.row243 node00396))) (add (add (add Basis07.row246 Basis07.row249) (add node04126 node01602)) (add (add Basis07.row254 Basis07.row255) (add node00419 node02890)))) (add (add (add (t Basis07.row260) (add (t Basis07.row261) (t Basis07.row262))) (add (add (t Basis07.row263) (t Basis07.row264)) (add node03914 node01794))) (add (add (add node00851 (t Basis07.row272)) (add Basis07.row274 node02447)) (add (add node02718 node01990) (add Basis07.row283 node03571))))) (add (add (add (add node01414 (add Basis07.row290 node01767)) (add (add node00921 Basis07.row295) (add (t Basis07.row295) node00207))) (add (add (add node02688 node02254) (add node03487 node03916)) (add (add Basis07.row309 (t Basis07.row309)) (add (t Basis07.row310) node03198)))) (add (add (add (t Basis07.row315) (add node03840 Basis07.row320)) (add (add node02982 node03760) (add node00803 node04045))) (add (add (add (t Basis07.row332) node01677) (add Basis07.row335 (t Basis07.row336))) (add (add (t Basis07.row339) node00542) (add (t Basis07.row342) Basis07.row343)))))) (add (add (add (add (add node02220 (add node00784 (t Basis07.row347))) (add (add (t Basis07.row348) (t Basis07.row349)) (add node02768 node00987))) (add (add (add node01415 (t Basis07.row357)) (add (t Basis07.row359) Basis07.row360)) (add (add (t Basis07.row361) node01029) (add Basis07.row364 (t Basis07.row365))))) (add (add (add (t Basis07.row366) (add Basis07.row367 (t Basis07.row368))) (add (add (t Basis07.row369) node01984) (add node01257 node01199))) (add (add (add Basis07.row376 (t Basis07.row376)) (add node00256 node01353)) (add (add Basis07.row384 Basis07.row385) (add Basis07.row386 node02736))))) (add (add (add (add node01049 (add node00423 Basis07.row392)) (add (add Basis07.row394 Basis07.row396) (add Basis07.row397 node03449))) (add (add (add (t Basis07.row400) (t Basis07.row401)) (add node00630 node01713)) (add (add Basis07.row407 (t Basis07.row407)) (add node01377 node02102)))) (add (add (add (add (t Basis07.row412) (t Basis07.row413)) (add node01931 node02025)) (add (add (t Basis07.row418) (t Basis07.row422)) (add Basis07.row423 Basis07.row424))) (add (add (add (t Basis07.row426) node01455) (add (t Basis07.row429) node01483)) (add (add node01456 Basis07.row435) (add (t Basis07.row435) node03260)))))))) (add (add (add (add (add (add (add node02520 (add (t Basis07.row442) Basis07.row445)) (add (add Basis07.row446 (t Basis07.row447)) (add Basis07.row449 (t Basis07.row450)))) (add (add (add Basis07.row452 (t Basis07.row452)) (add node02491 node02073)) (add (add node03884 (t Basis07.row460)) (add node00464 Basis07.row464)))) (add (add (add node00706 (add node03653 (t Basis07.row472))) (add (add (t Basis07.row473) Basis07.row474) (add Basis07.row476 Basis07.row478))) (add (add (add (t Basis07.row478) node02216) (add Basis07.row484 (t Basis07.row484))) (add (add (t Basis07.row485) (t Basis07.row486)) (add (t Basis07.row487) Basis07.row488))))) (add (add (add (add Basis07.row492 (add Basis07.row493 (t Basis07.row493))) (add (add node02004 Basis07.row498) (add node01076 node02030))) (add (add (add node01606 node00429) (add node01662 node02844)) (add (add node01368 Basis07.row512) (add node02378 (t Basis07.row515))))) (add (add (add node00740 (add (t Basis07.row518) Basis07.row520)) (add (add Basis07.row522 node03661) (add (t Basis07.row525) (t Basis07.row526)))) (add (add (add (t Basis07.row528) Basis07.row529) (add node00156 node01721)) (add (add node01196 Basis07.row536) (add node03721 node00275)))))) (add (add (add (add (add (t Basis07.row543) (add (t Basis07.row544) node01127)) (add (add node00932 Basis07.row551) (add (t Basis07.row551) Basis07.row554))) (add (add (add Basis07.row555 node02296) (add (t Basis07.row561) node04311)) (add (add node02318 (t Basis07.row568)) (add node03345 Basis07.row572)))) (add (add (add node02522 (add Basis07.row578 (t Basis07.row579))) (add (add Basis07.row581 node02528) (add (t Basis07.row585) (t Basis07.row587)))) (add (add (add Basis07.row588 (t Basis07.row589)) (add node03568 node02070)) (add (add Basis07.row597 node00489) (add Basis07.row599 (t Basis07.row601)))))) (add (add (add (add node01843 (add node00764 node00964)) (add (add node00183 node04180) (add Basis07.row615 Basis07.row617))) (add (add (add Basis07.row618 node01055) (add (t Basis07.row620) (t Basis07.row621))) (add (add (t Basis07.row625) Basis07.row626) (add (t Basis07.row627) (t Basis07.row628))))) (add (add (add (add Basis07.row630 Basis07.row634) (add (t Basis07.row634) node00618)) (add (add node00405 node01723) (add node00854 node01799))) (add (add (add (t Basis07.row647) Basis07.row648) (add Basis07.row650 (t Basis07.row650))) (add (add node01812 node00577) (add node01370 (t Basis07.row660)))))))) (add (add (add (add (add (add Basis07.row662 (add node00245 (t Basis07.row669))) (add (add (t Basis07.row670) (t Basis07.row672)) (add Basis07.row675 (t Basis07.row676)))) (add (add (add (t Basis07.row679) (t Basis07.row680)) (add node01319 node02416)) (add (add (t Basis07.row688) Basis07.row689) (add (t Basis07.row690) node01666)))) (add (add (add (t Basis07.row694) (add Basis07.row696 node00434)) (add (add Basis07.row700 (t Basis07.row700)) (add node01498 (t Basis07.row704)))) (add (add (add node00374 node00929) (add node03319 node01438)) (add (add node01902 node02174) (add (t Basis07.row717) Basis07.row719))))) (add (add (add (add node02352 (add Basis07.row723 Basis07.row724)) (add (add Basis07.row725 Basis07.row727) (add (t Basis07.row728) node01407))) (add (add (add node03418 (t Basis07.row734)) (add node03608 (t Basis07.row737))) (add (add node00938 node02544) (add node01182 (t Basis07.row745))))) (add (add (add (t Basis07.row746) (add node00263 Basis07.row752)) (add (add Basis07.row753 node01850) (add (t Basis07.row758) (t Basis07.row759)))) (add (add (add node00841 Basis07.row762) (add (t Basis07.row762) node00264)) (add (add (t Basis07.row765) Basis07.row766) (add node00388 Basis07.row771)))))) (add (add (add (add (add Basis07.row772 (add (t Basis07.row772) node00102)) (add (add node00984 node02664) (add node00493 node00453))) (add (add (add node02270 node00030) (add (t Basis07.row789) (t Basis07.row790))) (add (add Basis07.row792 node00684) (add Basis07.row797 node03966)))) (add (add (add Basis07.row801 (add node02548 node03621)) (add (add node00454 node02645) (add node02814 (t Basis07.row816)))) (add (add (add node01081 node00547) (add node00202 Basis07.row825)) (add (add node03073 (t Basis07.row828)) (add node00532 Basis07.row833))))) (add (add (add (add node00880 (add node03221 Basis07.row844)) (add (add node02214 Basis07.row847) (add Basis07.row848 (t Basis07.row848)))) (add (add (add node02465 node00752) (add node00675 Basis07.row857)) (add (add Basis07.row859 (t Basis07.row860)) (add node00876 node01020)))) (add (add (add (add node01378 node04437) (add Basis07.row872 Basis07.row873)) (add (add Basis07.row874 Basis07.row876) (add (t Basis07.row877) (t Basis07.row880)))) (add (add (add Basis07.row884 node00605) (add node00719 node00960)) (add (add node00235 Basis07.row893) (add Basis07.row894 Basis07.row895)))))))))

private theorem row217 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 217 (0, 0)) ((rowsAt 10).getD 217 (0, 0)) := by
  apply of_certificate witness217
  · decide +kernel
  · decide +kernel

private noncomputable def witness218 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row060

private theorem row218 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 218 (0, 0)) ((rowsAt 10).getD 218 (0, 0)) := by
  apply of_certificate witness218
  · decide +kernel
  · decide +kernel

private noncomputable def witness219 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add Basis07.row000 (add node02364 node00776)) (add (add (t Basis07.row005) node03077) (add (t Basis07.row010) Basis07.row012))) (add (add node00822 (add node02932 node01360)) (add (add node01147 node00634) (add Basis07.row024 Basis07.row028)))) (add (add (add (t Basis07.row030) (add (t Basis07.row031) Basis07.row036)) (add (add node03582 Basis07.row040) (add node02040 node01942))) (add (add (add node03553 Basis07.row049) (add Basis07.row050 node01644)) (add (add node00510 node00072) (add (t Basis07.row058) (t Basis07.row061)))))) (add (add (add (add node02402 (add node00391 (t Basis07.row066))) (add (add node00661 node02860) (add (t Basis07.row073) (t Basis07.row074)))) (add (add (add Basis07.row075 Basis07.row078) (add Basis07.row079 node04243)) (add (add (t Basis07.row082) Basis07.row083) (add Basis07.row084 node03098)))) (add (add (add (t Basis07.row087) (add node01021 Basis07.row091)) (add (add Basis07.row092 node03433) (add node02182 node02478))) (add (add (add (t Basis07.row099) (t Basis07.row100)) (add Basis07.row103 (t Basis07.row103))) (add (add Basis07.row106 node00513) (add node02407 Basis07.row110)))))) (add (add (add (add (add Basis07.row111 (add Basis07.row113 (t Basis07.row114))) (add (add node00286 (t Basis07.row117)) (add (t Basis07.row118) node01386))) (add (add (add node02973 node03729) (add Basis07.row127 Basis07.row129)) (add (add node00075 Basis07.row131) (add Basis07.row132 (t Basis07.row135))))) (add (add (add node01113 (add (t Basis07.row141) Basis07.row144)) (add (add (t Basis07.row144) (t Basis07.row146)) (add (t Basis07.row147) (t Basis07.row148)))) (add (add (add node04398 node01308) (add node02763 Basis07.row158)) (add (add (t Basis07.row162) Basis07.row163) (add node00180 node00892))))) (add (add (add (add node01648 (add node00045 (t Basis07.row171))) (add (add node02307 (t Basis07.row176)) (add node00334 node00056))) (add (add (add (t Basis07.row181) (t Basis07.row182)) (add (t Basis07.row183) Basis07.row184)) (add (add node02429 node00802) (add node01705 node00833)))) (add (add (add node00240 (add Basis07.row195 Basis07.row196)) (add (add node00650 node00893) (add (t Basis07.row200) (t Basis07.row202)))) (add (add (add node03297 Basis07.row207) (add (t Basis07.row207) (t Basis07.row208))) (add (add node01334 node01621) (add node02852 (t Basis07.row217)))))))) (add (add (add (add (add (add node01600 (add Basis07.row223 node03045)) (add (add (t Basis07.row226) Basis07.row228) (add Basis07.row229 (t Basis07.row232)))) (add (add Basis07.row233 (add Basis07.row234 (t Basis07.row235))) (add (add (t Basis07.row236) node00678) (add node00095 (t Basis07.row241))))) (add (add (add Basis07.row243 (add node00148 (t Basis07.row246))) (add (add node00458 Basis07.row251) (add (t Basis07.row253) node01464))) (add (add (add node01045 node00679) (add Basis07.row262 Basis07.row263)) (add (add (t Basis07.row263) (t Basis07.row265)) (add Basis07.row266 Basis07.row267))))) (add (add (add (add node01825 (add (t Basis07.row270) Basis07.row272)) (add (add node01121 node03518) (add Basis07.row279 Basis07.row284))) (add (add (add Basis07.row285 (t Basis07.row285)) (add node01446 node02051)) (add (add Basis07.row291 Basis07.row292) (add node01046 node01365)))) (add (add (add (t Basis07.row297) (add (t Basis07.row298) (t Basis07.row299))) (add (add Basis07.row300 node02574) (add node00695 node02965))) (add (add (add node00399 node01769) (add node00290 Basis07.row312)) (add (add Basis07.row313 node04130) (add node00834 Basis07.row318)))))) (add (add (add (add (add (t Basis07.row318) (add Basis07.row320 (t Basis07.row320))) (add (add node02927 Basis07.row325) (add node04131 node00989))) (add (add (add node03658 node00980) (add (t Basis07.row337) node01653)) (add (add Basis07.row341 node00016) (add node02663 node03891)))) (add (add (add node02287 (add node00059 node01415)) (add (add node00077 (t Basis07.row358)) (add Basis07.row359 Basis07.row360))) (add (add (add (t Basis07.row360) (t Basis07.row362)) (add node04178 node00226)) (add (add node01335 Basis07.row371) (add (t Basis07.row372) (t Basis07.row373)))))) (add (add (add (add (t Basis07.row375) (add (t Basis07.row377) node03259)) (add (add node00193 node03807) (add node00809 (t Basis07.row389)))) (add (add (add (t Basis07.row393) Basis07.row395) (add node01957 Basis07.row398)) (add (add node03575 Basis07.row402) (add Basis07.row403 Basis07.row404)))) (add (add (add node01714 (add node02360 Basis07.row411)) (add (add Basis07.row412 node04005) (add node02910 node00721))) (add (add (add node01013 (t Basis07.row421)) (add (t Basis07.row422) node00910)) (add (add node01114 node01455) (add node00552 node01835)))))))) (add (add (add (add (add (add (add node02842 (add node00138 (t Basis07.row437))) (add (add node02719 node00427) (add (t Basis07.row442) node02998))) (add (add Basis07.row447 (add Basis07.row448 node00828)) (add (add node02960 (t Basis07.row452)) (add node01379 node00260)))) (add (add (add node02853 (add node02333 node00464)) (add (add Basis07.row464 node03159) (add node02659 node00614))) (add (add (add node00316 node00368) (add node00884 node02129)) (add (add node00525 node00154) (add node01107 node00553))))) (add (add (add (add node01395 (add node04260 node01870)) (add (add node00587 node00110) (add node02030 (t Basis07.row505)))) (add (add (add (t Basis07.row506) (t Basis07.row507)) (add node02265 (t Basis07.row510))) (add (add node02700 node02350) (add (t Basis07.row516) node01188)))) (add (add (add Basis07.row519 (add node00125 (t Basis07.row522))) (add (add node03062 Basis07.row528) (add node00655 Basis07.row532))) (add (add (add Basis07.row533 Basis07.row534) (add (t Basis07.row534) node01663)) (add (add node01232 node00601) (add node01036 (t Basis07.row541))))))) (add (add (add (add (add Basis07.row543 (add node01127 node01052)) (add (add node03024 node04142) (add node01077 (t Basis07.row557)))) (add (add (add (t Basis07.row560) node01181) (add node01258 (t Basis07.row566))) (add (add node00823 node01734) (add node02398 node00742)))) (add (add (add node02007 (add (t Basis07.row579) (t Basis07.row580))) (add (add Basis07.row584 (t Basis07.row584)) (add (t Basis07.row588) Basis07.row589))) (add (add (add (t Basis07.row589) node00820) (add node00229 node03657)) (add (add node00527 Basis07.row603) (add (t Basis07.row603) Basis07.row606))))) (add (add (add (add node00964 (add node02116 node00140)) (add (add (t Basis07.row613) Basis07.row616) (add Basis07.row618 (t Basis07.row618)))) (add (add (add node03482 (t Basis07.row623)) (add (t Basis07.row626) Basis07.row628)) (add (add (t Basis07.row630) (t Basis07.row631)) (add node00469 node04465)))) (add (add (add node01527 (add Basis07.row640 node02455)) (add (add Basis07.row645 (t Basis07.row647)) (add node02300 node00974))) (add (add (add node01488 node00577) (add Basis07.row657 node02781)) (add (add (t Basis07.row661) node00433) (add node02438 node03268))))))) (add (add (add (add (add (add node00944 (add node01270 node01846)) (add (add (t Basis07.row676) (t Basis07.row677)) (add Basis07.row680 Basis07.row682))) (add (add (add (t Basis07.row682) node03214) (add (t Basis07.row686) node03604)) (add (add (t Basis07.row691) node03396) (add node01580 (t Basis07.row698))))) (add (add (add Basis07.row699 (add node03579 node04085)) (add (add Basis07.row706 (t Basis07.row707)) (add Basis07.row709 node01438))) (add (add (add Basis07.row714 Basis07.row716) (add node01490 (t Basis07.row719))) (add (add Basis07.row721 (t Basis07.row722)) (add node00801 node02120))))) (add (add (add (add node02543 (add node04189 (t Basis07.row734))) (add (add (t Basis07.row735) node00216) (add (t Basis07.row741) Basis07.row743))) (add (add (add node03167 node01781) (add node00296 Basis07.row751)) (add (add Basis07.row752 node00327) (add node00788 node00797)))) (add (add (add Basis07.row763 (add Basis07.row766 node02467)) (add (add (t Basis07.row769) (t Basis07.row770)) (add (t Basis07.row771) node03889))) (add (add (add node03577 Basis07.row778) (add node02139 node03429)) (add (add Basis07.row783 Basis07.row784) (add Basis07.row786 (t Basis07.row787))))))) (add (add (add (add (add (t Basis07.row788) (add (t Basis07.row789) node00509)) (add (add Basis07.row792 node03637) (add node01404 node00743))) (add (add (add Basis07.row800 node02259) (add (t Basis07.row805) node03712)) (add (add node00454 node00143) (add (t Basis07.row812) node00986)))) (add (add (add Basis07.row815 (add Basis07.row816 Basis07.row818)) (add (add node00659 Basis07.row821) (add (t Basis07.row821) Basis07.row824))) (add (add (add (t Basis07.row824) Basis07.row825) (add node02388 node00690)) (add (add node00532 node00494) (add node02925 Basis07.row836))))) (add (add (add (add (t Basis07.row836) (add node03700 Basis07.row844)) (add (add Basis07.row845 (t Basis07.row845)) (add Basis07.row847 Basis07.row848))) (add (add (add (t Basis07.row848) Basis07.row850) (add node04432 node01425)) (add (add node00624 node02580) (add node01786 node02882)))) (add (add (add node04434 (add node01796 node01787)) (add (add node00646 Basis07.row874) (add Basis07.row877 Basis07.row879))) (add (add (add node03088 Basis07.row883) (add (t Basis07.row885) node03325)) (add (add node01737 (t Basis07.row892)) (add (t Basis07.row893) Basis07.row895)))))))))

private theorem row219 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 219 (0, 0)) ((rowsAt 10).getD 219 (0, 0)) := by
  apply of_certificate witness219
  · decide +kernel
  · decide +kernel

private noncomputable def witness220 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add node00582 (add node01241 node02257)) (add (add (t Basis07.row005) node01102) (add node02762 (t Basis07.row010)))) (add (add (add Basis07.row013 Basis07.row014) (add node00190 (t Basis07.row016))) (add (add Basis07.row021 (t Basis07.row021)) (add node02090 node00918)))) (add (add (add (add node02091 (t Basis07.row028)) (add node01928 (t Basis07.row032))) (add (add node00266 node04389) (add (t Basis07.row039) (t Basis07.row040)))) (add (add (add Basis07.row041 (t Basis07.row041)) (add node01942 node00908)) (add (add Basis07.row047 Basis07.row048) (add Basis07.row049 node02770))))) (add (add (add (add node01758 (add Basis07.row054 Basis07.row055)) (add (add Basis07.row057 node01578) (add (t Basis07.row060) Basis07.row061))) (add (add (add Basis07.row062 Basis07.row063) (add (t Basis07.row064) Basis07.row066)) (add (add (t Basis07.row068) node02368) (add node01943 (t Basis07.row073))))) (add (add (add (add node01008 (t Basis07.row076)) (add node01306 node00134)) (add (add (t Basis07.row082) (t Basis07.row083)) (add node00747 (t Basis07.row087)))) (add (add (add (t Basis07.row088) (t Basis07.row090)) (add Basis07.row091 Basis07.row094)) (add (add (t Basis07.row094) node00360) (add (t Basis07.row100) node01760)))))) (add (add (add (add (add node01339 (add node03754 node01394)) (add (add Basis07.row112 (t Basis07.row114)) (add (t Basis07.row116) node01074))) (add (add (add (t Basis07.row119) (t Basis07.row120)) (add (t Basis07.row121) node00840)) (add (add Basis07.row125 node01597) (add (t Basis07.row128) node02668)))) (add (add (add (add node00847 node03755) (add node04450 (t Basis07.row138))) (add (add (t Basis07.row139) node01820) (add Basis07.row143 Basis07.row144))) (add (add (add (t Basis07.row144) (t Basis07.row145)) (add Basis07.row148 (t Basis07.row149))) (add (add (t Basis07.row151) (t Basis07.row152)) (add Basis07.row153 node01690))))) (add (add (add (add node03882 (add Basis07.row158 node03967)) (add (add (t Basis07.row163) Basis07.row166) (add node00571 node03184))) (add (add (add node03039 (t Basis07.row176)) (add Basis07.row177 node03171)) (add (add node00239 node02047) (add (t Basis07.row184) node01472)))) (add (add (add (add Basis07.row187 node01320) (add node00271 node00005)) (add (add Basis07.row197 Basis07.row198) (add node01136 node01044))) (add (add (add node00826 node01291) (add (t Basis07.row207) node01749)) (add (add (t Basis07.row211) (t Basis07.row212)) (add node01382 node01153))))))) (add (add (add (add (add (add node02760 (add (t Basis07.row220) (t Basis07.row221))) (add (add (t Basis07.row224) Basis07.row226) (add Basis07.row227 Basis07.row228))) (add (add (add Basis07.row231 (t Basis07.row233)) (add (t Basis07.row234) (t Basis07.row236))) (add (add (t Basis07.row238) node01583) (add Basis07.row242 (t Basis07.row242))))) (add (add (add (add Basis07.row243 node01623) (add node02807 (t Basis07.row248))) (add (add (t Basis07.row250) Basis07.row251) (add (t Basis07.row252) Basis07.row254))) (add (add (add Basis07.row255 Basis07.row257) (add Basis07.row258 (t Basis07.row260))) (add (add node01341 node02570) (add node01228 node00254))))) (add (add (add (add (t Basis07.row270) (add Basis07.row271 (t Basis07.row273))) (add (add (t Basis07.row274) Basis07.row275) (add node02447 node00539))) (add (add (add node01558 Basis07.row281) (add node03649 node00540)) (add (add Basis07.row288 node02051) (add node01537 Basis07.row294)))) (add (add (add (add Basis07.row296 (t Basis07.row296)) (add node01110 node00022)) (add (add node02871 node04448) (add node00047 node02474))) (add (add (add (t Basis07.row311) node00119) (add Basis07.row318 node00136)) (add (add (t Basis07.row320) (t Basis07.row322)) (add node01503 (t Basis07.row326))))))) (add (add (add (add (add Basis07.row327 (add node03106 (t Basis07.row331))) (add (add Basis07.row332 node02207) (add node03469 Basis07.row337))) (add (add (add node02286 node02052) (add node01309 node00784)) (add (add node01829 Basis07.row350) (add (t Basis07.row353) node00611)))) (add (add (add (add (t Basis07.row357) node01878) (add (t Basis07.row360) (t Basis07.row361))) (add (add (t Basis07.row362) Basis07.row363) (add Basis07.row365 node00845))) (add (add (add node01561 node01478) (add (t Basis07.row372) Basis07.row377)) (add (add node00793 node00896) (add node02635 node00981))))) (add (add (add (add node00461 (add node01277 (t Basis07.row393))) (add (add node01098 Basis07.row396) (add Basis07.row397 node03718))) (add (add (add node00123 node00869) (add node02055 node00445)) (add (add node02737 node02346) (add Basis07.row411 node02699)))) (add (add (add (add node00463 node04192) (add Basis07.row419 Basis07.row420)) (add (add (t Basis07.row420) node00565) (add node00910 node01114))) (add (add (add node01455 node00338) (add node04411 (t Basis07.row437))) (add (add node03567 (t Basis07.row440)) (add node04042 node01689)))))))) (add (add (add (add (add (add (add node00640 (add Basis07.row449 node03346)) (add (add Basis07.row452 (t Basis07.row452)) (add node02491 node00315))) (add (add (add (t Basis07.row457) Basis07.row464) (add node02804 (t Basis07.row469))) (add (add node03021 Basis07.row473) (add Basis07.row474 Basis07.row475)))) (add (add (add (add (t Basis07.row475) node02074) (add node00341 Basis07.row481)) (add (add node00154 Basis07.row485) (add node01863 (t Basis07.row487)))) (add (add (add node02989 node03846) (add (t Basis07.row494) node01445)) (add (add node00110 node02030) (add node01354 node00382))))) (add (add (add (add node04416 (add node02844 (t Basis07.row510))) (add (add node01485 node00174) (add Basis07.row515 (t Basis07.row516)))) (add (add (add Basis07.row517 node01188) (add node01072 node01356)) (add (add node00897 node03626) (add (t Basis07.row526) node00261)))) (add (add (add (add (t Basis07.row530) Basis07.row531) (add node02156 node01196)) (add (add (t Basis07.row535) (t Basis07.row536)) (add (t Basis07.row537) Basis07.row538))) (add (add (add Basis07.row539 Basis07.row540) (add (t Basis07.row541) (t Basis07.row543))) (add (add (t Basis07.row544) node03012) (add node01421 Basis07.row550)))))) (add (add (add (add (add Basis07.row551 (add node00450 node01289)) (add (add node00933 node02163) (add node00934 node04070))) (add (add (add Basis07.row565 Basis07.row566) (add node03329 Basis07.row570)) (add (add node01348 node01358) (add (t Basis07.row574) (t Basis07.row576))))) (add (add (add (add Basis07.row577 Basis07.row578) (add (t Basis07.row579) Basis07.row581)) (add (add Basis07.row582 node01642) (add node00343 node01169))) (add (add (add node00212 Basis07.row595) (add node01524 Basis07.row600)) (add (add Basis07.row602 node02298) (add (t Basis07.row604) (t Basis07.row605)))))) (add (add (add (add node01210 (add Basis07.row609 node01743)) (add (add Basis07.row612 (t Basis07.row613)) (add Basis07.row616 node02914))) (add (add (add Basis07.row619 node04313) (add node01643 (t Basis07.row625))) (add (add (t Basis07.row626) Basis07.row628) (add (t Basis07.row628) (t Basis07.row630))))) (add (add (add (add (t Basis07.row633) node02837) (add node01526 node00167)) (add (add Basis07.row640 node02455) (add Basis07.row644 Basis07.row645))) (add (add (add Basis07.row646 (t Basis07.row648)) (add (t Basis07.row649) node00974)) (add (add Basis07.row655 node02242) (add Basis07.row660 (t Basis07.row661)))))))) (add (add (add (add (add (add Basis07.row662 (add node01056 (t Basis07.row665))) (add (add node03069 node00836) (add (t Basis07.row672) node00246))) (add (add (add Basis07.row676 (t Basis07.row677)) (add node02943 Basis07.row682)) (add (add (t Basis07.row683) (t Basis07.row684)) (add Basis07.row685 (t Basis07.row688))))) (add (add (add (add Basis07.row690 node02338) (add (t Basis07.row695) Basis07.row698)) (add (add (t Basis07.row700) Basis07.row702) (add Basis07.row704 Basis07.row705))) (add (add (add Basis07.row706 Basis07.row708) (add (t Basis07.row708) (t Basis07.row712))) (add (add node00619 node01462) (add node03399 Basis07.row719))))) (add (add (add (add Basis07.row721 (add Basis07.row722 node01611)) (add (add (t Basis07.row725) (t Basis07.row726)) (add node02120 Basis07.row730))) (add (add (add node01186 node01849) (add (t Basis07.row735) Basis07.row737)) (add (add (t Basis07.row737) (t Basis07.row738)) (add node04021 node01080)))) (add (add (add (add node00756 node00003) (add node02071 Basis07.row752)) (add (add node01850 node00788) (add (t Basis07.row758) (t Basis07.row760)))) (add (add (add Basis07.row761 node00603) (add Basis07.row765 Basis07.row766)) (add (add Basis07.row767 node01573) (add node00353 (t Basis07.row772))))))) (add (add (add (add (add node03545 (add Basis07.row777 (t Basis07.row777))) (add (add (t Basis07.row778) node01635) (add Basis07.row782 (t Basis07.row784)))) (add (add (add (t Basis07.row785) (t Basis07.row786)) (add (t Basis07.row787) Basis07.row789)) (add (add node02316 node02458) (add node03189 node02249)))) (add (add (add (add node00743 Basis07.row800) (add Basis07.row801 node00410)) (add (add (t Basis07.row805) Basis07.row806) (add node03147 (t Basis07.row811)))) (add (add (add Basis07.row812 node00622) (add node02602 node00547)) (add (add node00202 node02344) (add node03546 node00604))))) (add (add (add (add (add Basis07.row830 Basis07.row831) (add node04324 node03403)) (add (add Basis07.row837 (t Basis07.row840)) (add node01337 (t Basis07.row843)))) (add (add (add node00412 node01216) (add Basis07.row849 Basis07.row851)) (add (add node04155 node02580) (add node01301 node01227)))) (add (add (add (add node00203 node01378) (add Basis07.row868 Basis07.row871)) (add (add node00646 node01264) (add node02949 Basis07.row880))) (add (add (add Basis07.row883 (t Basis07.row883)) (add (t Basis07.row884) node02089)) (add (add node01193 node02253) (add Basis07.row892 Basis07.row893)))))))))

private theorem row220 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 220 (0, 0)) ((rowsAt 10).getD 220 (0, 0)) := by
  apply of_certificate witness220
  · decide +kernel
  · decide +kernel

private noncomputable def witness221 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row061

private theorem row221 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 221 (0, 0)) ((rowsAt 10).getD 221 (0, 0)) := by
  apply of_certificate witness221
  · decide +kernel
  · decide +kernel

private noncomputable def witness222 : Cert (n := 896) (rowsAt 7) :=
  (add (add (add (add (add (add (add (add node01241 (add (t Basis07.row003) Basis07.row004)) (add (add node04105 node01064) (add node00591 node00822))) (add (add node00190 (add Basis07.row020 node01147)) (add (add node02533 node00918) (add node02323 (t Basis07.row028))))) (add (add (add node03559 (add Basis07.row032 node00283)) (add (add node03413 node01120) (add (t Basis07.row041) (t Basis07.row042)))) (add (add (add node00607 node00908) (add node02172 (t Basis07.row049))) (add (add node02599 node00583) (add (t Basis07.row056) node00267))))) (add (add (add (add node00249 (add node01294 node00391)) (add (add node01375 node02041) (add node04296 Basis07.row073))) (add (add (add Basis07.row076 node02889) (add node00134 node02066)) (add (add (t Basis07.row083) (t Basis07.row084)) (add node03250 Basis07.row088)))) (add (add (add node01021 (add node02583 node03081)) (add (add Basis07.row096 (t Basis07.row097)) (add node03550 node02093))) (add (add (add Basis07.row104 Basis07.row106) (add (t Basis07.row106) Basis07.row108)) (add (add Basis07.row109 node01435) (add (t Basis07.row112) (t Basis07.row120))))))) (add (add (add (add (add (t Basis07.row121) (add node00949 (t Basis07.row124))) (add (add Basis07.row126 node01880) (add node00075 node00457))) (add (add (add node00847 node01005) (add Basis07.row136 node02044)) (add (add (t Basis07.row139) Basis07.row142) (add Basis07.row143 node01065)))) (add (add (add node00287 (add node01933 Basis07.row154)) (add (add (t Basis07.row155) node00976) (add node04343 node00537))) (add (add (add node02739 node00760) (add node02370 Basis07.row170)) (add (add Basis07.row171 Basis07.row173) (add node01468 Basis07.row176))))) (add (add (add (add (t Basis07.row177) (add node00056 node02227)) (add (add Basis07.row182 Basis07.row184) (add Basis07.row185 Basis07.row186))) (add (add (add node01238 node01320) (add (t Basis07.row190) node00240)) (add (add node02530 node01950) (add node03911 Basis07.row203)))) (add (add (add Basis07.row204 (add (t Basis07.row205) (t Basis07.row209))) (add (add (t Basis07.row210) node00538) (add node01172 node02958))) (add (add (add node01453 node00704) (add (t Basis07.row224) (t Basis07.row225))) (add (add node01364 node03176) (add node02145 (t Basis07.row237)))))))) (add (add (add (add (add (add (t Basis07.row239) (add Basis07.row240 node00418)) (add (add Basis07.row243 (t Basis07.row245)) (add (t Basis07.row246) node02614))) (add (add (t Basis07.row250) (add node01891 node01318)) (add (add node00419 Basis07.row258) (add node03298 node00366)))) (add (add (add (t Basis07.row263) (add (t Basis07.row264) (t Basis07.row265))) (add (add Basis07.row268 node01825) (add Basis07.row271 node00519))) (add (add (add Basis07.row276 Basis07.row277) (add node02037 Basis07.row282)) (add (add (t Basis07.row283) node01037) (add node00540 Basis07.row288))))) (add (add (add (add node01972 (add (t Basis07.row291) node04211)) (add (add node02035 node01100) (add (t Basis07.row299) node01392))) (add (add (add (t Basis07.row305) node01207) (add node00225 node02255)) (add (add Basis07.row311 Basis07.row312) (add Basis07.row313 node02772)))) (add (add (add node03374 (add Basis07.row321 node02773)) (add (add (t Basis07.row325) Basis07.row327) (add node02519 node04441))) (add (add (add Basis07.row334 node00930) (add (t Basis07.row338) (t Basis07.row339))) (add (add (t Basis07.row340) (t Basis07.row341)) (add Basis07.row342 Basis07.row344)))))) (add (add (add (add (add Basis07.row345 (add Basis07.row346 node01829)) (add (add node01218 node03683) (add node03633 Basis07.row357))) (add (add (add node01416 node00182) (add node03494 (t Basis07.row366))) (add (add node01997 node00335) (add node00848 node01637)))) (add (add (add (t Basis07.row377) (add node03201 node01655)) (add (add node04187 node00981) (add node02351 (t Basis07.row392)))) (add (add (add (t Basis07.row393) Basis07.row394) (add (t Basis07.row394) node02028)) (add (add node03449 node01711) (add Basis07.row403 (t Basis07.row403)))))) (add (add (add (add (t Basis07.row405) (add node00705 Basis07.row412)) (add (add node00564 node01454) (add node01321 node04247))) (add (add (add (t Basis07.row422) Basis07.row425) (add (t Basis07.row425) node02377)) (add (add (t Basis07.row429) node01483) (add node00258 Basis07.row434)))) (add (add (add node03260 (add node01742 node03668)) (add (add Basis07.row445 node00653) (add node01184 Basis07.row450))) (add (add (add (t Basis07.row452) (t Basis07.row454)) (add Basis07.row456 (t Basis07.row456))) (add (add (t Basis07.row458) (t Basis07.row459)) (add node01881 Basis07.row463)))))))) (add (add (add (add (add (add (add node01418 (add node03484 (t Basis07.row471))) (add (add Basis07.row472 Basis07.row473) (add Basis07.row475 Basis07.row477))) (add (add Basis07.row478 (add Basis07.row479 Basis07.row480)) (add (add (t Basis07.row480) node01185) (add node02738 node00813)))) (add (add (add Basis07.row490 (add node00885 Basis07.row494)) (add (add Basis07.row496 Basis07.row497) (add node03825 node02030))) (add (add (add Basis07.row505 node00739) (add node01310 (t Basis07.row510))) (add (add (t Basis07.row511) node02700) (add node01469 node01015))))) (add (add (add (add node04356 (add Basis07.row520 node01356)) (add (add node00643 Basis07.row527) (add node01929 node04160))) (add (add (add (t Basis07.row533) (t Basis07.row534)) (add node00431 node00544)) (add (add node04011 (t Basis07.row541)) (add (t Basis07.row543) Basis07.row546)))) (add (add (add (t Basis07.row546) (add Basis07.row547 Basis07.row550)) (add (add node00449 (t Basis07.row553)) (add node00933 node01618))) (add (add (add node00934 Basis07.row561) (add (t Basis07.row562) (t Basis07.row563))) (add (add (t Basis07.row565) (t Basis07.row566)) (add (t Basis07.row567) node00823)))))) (add (add (add (add (add node00665 (add (t Basis07.row575) node00070)) (add (add node00101 node00304) (add node04145 Basis07.row586))) (add (add (add Basis07.row589 (t Basis07.row589)) (add (t Basis07.row590) Basis07.row593)) (add (add (t Basis07.row593) node03310) (add node00956 node01803)))) (add (add (add node01189 (add node01629 node01814)) (add (add (t Basis07.row606) Basis07.row607) (add node00183 node01743))) (add (add (add node03342 Basis07.row617) (add node02684 node00184)) (add (add node00716 node02629) (add node01205 (t Basis07.row627)))))) (add (add (add (add (t Basis07.row628) (add (t Basis07.row630) node01610)) (add (add node00384 Basis07.row634) (add (t Basis07.row634) node03498))) (add (add (add (t Basis07.row638) node02299) (add Basis07.row641 Basis07.row644)) (add (add node02240 (t Basis07.row647)) (add node02132 node00923)))) (add (add (add node01778 (add Basis07.row655 node00112)) (add (add node00407 node01275) (add node00928 (t Basis07.row664)))) (add (add (add Basis07.row665 node00924) (add (t Basis07.row668) Basis07.row669)) (add (add node00836 node01632) (add (t Basis07.row674) (t Basis07.row675)))))))) (add (add (add (add (add (add node00917 (add node03009 node00936)) (add (add (t Basis07.row682) node03393) (add node00734 node04168))) (add (add (add Basis07.row691 node01371) (add node02823 node02078)) (add (add Basis07.row698 Basis07.row701) (add node01570 node00324)))) (add (add (add Basis07.row706 (add Basis07.row708 Basis07.row709)) (add (add Basis07.row714 (t Basis07.row715)) (add (t Basis07.row717) (t Basis07.row719)))) (add (add (add node01299 node01903) (add Basis07.row725 (t Basis07.row725))) (add (add node01141 Basis07.row728) (add Basis07.row731 Basis07.row732))))) (add (add (add (add (t Basis07.row734) (add Basis07.row735 (t Basis07.row736))) (add (add Basis07.row737 Basis07.row738) (add (t Basis07.row740) node01622))) (add (add (add node01331 node00217) (add node02564 node02071)) (add (add node00130 node03697) (add node04025 node01384)))) (add (add (add Basis07.row762 (add (t Basis07.row762) node00603)) (add (add Basis07.row766 Basis07.row768) (add Basis07.row770 (t Basis07.row771)))) (add (add (add (t Basis07.row772) node02167) (add node01613 Basis07.row778)) (add (add node02664 node03431) (add (t Basis07.row785) (t Basis07.row786))))))) (add (add (add (add (add node01908 (add node02385 Basis07.row792)) (add (add Basis07.row793 node02341) (add Basis07.row797 Basis07.row799))) (add (add (add node01989 (t Basis07.row804)) (add (t Basis07.row806) node00816)) (add (add node04290 Basis07.row811) (add (t Basis07.row813) node02343)))) (add (add (add Basis07.row817 (add Basis07.row818 (t Basis07.row818))) (add (add node00919 (t Basis07.row821)) (add node02344 (t Basis07.row825)))) (add (add (add node03220 Basis07.row829) (add node02126 node03084)) (add (add node00880 (t Basis07.row835)) (add node00862 (t Basis07.row838)))))) (add (add (add (add (t Basis07.row839) (add Basis07.row840 node01616)) (add (add Basis07.row845 Basis07.row846) (add node03507 node01630))) (add (add (add node00413 node00189) (add node01572 node00675)) (add (add Basis07.row857 node03350) (add node00746 node03941)))) (add (add (add node01500 (add node00941 node02204)) (add (add node00204 node00646) (add (t Basis07.row874) node00331))) (add (add (add node01060 node03408) (add (t Basis07.row882) node00455)) (add (add (t Basis07.row887) node00960) (add node02423 node02612)))))))))

private theorem row222 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 222 (0, 0)) ((rowsAt 10).getD 222 (0, 0)) := by
  apply of_certificate witness222
  · decide +kernel
  · decide +kernel

private noncomputable def witness223 : Cert (n := 896) (rowsAt 7) :=
  Basis07.row528

private theorem row223 : Good (n := 896) (rowsAt 7)
    ((rowsAt 7).getD 223 (0, 0)) ((rowsAt 10).getD 223 (0, 0)) := by
  apply of_certificate witness223
  · decide +kernel
  · decide +kernel

private theorem block00 (i : ℕ) (hl : 0 ≤ i) (hu : i < 28) :
    Good (n := 896) (rowsAt 7) ((rowsAt 7).getD i (0, 0)) ((rowsAt 10).getD i (0, 0)) := by
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
    Good (n := 896) (rowsAt 7) ((rowsAt 7).getD i (0, 0)) ((rowsAt 10).getD i (0, 0)) := by
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
    Good (n := 896) (rowsAt 7) ((rowsAt 7).getD i (0, 0)) ((rowsAt 10).getD i (0, 0)) := by
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
    Good (n := 896) (rowsAt 7) ((rowsAt 7).getD i (0, 0)) ((rowsAt 10).getD i (0, 0)) := by
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
    Good (n := 896) (rowsAt 7) ((rowsAt 7).getD i (0, 0)) ((rowsAt 10).getD i (0, 0)) := by
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
    Good (n := 896) (rowsAt 7) ((rowsAt 7).getD i (0, 0)) ((rowsAt 10).getD i (0, 0)) := by
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
    Good (n := 896) (rowsAt 7) ((rowsAt 7).getD i (0, 0)) ((rowsAt 10).getD i (0, 0)) := by
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
    Good (n := 896) (rowsAt 7) ((rowsAt 7).getD i (0, 0)) ((rowsAt 10).getD i (0, 0)) := by
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
    Good (n := 896) (rowsAt 7) ((rowsAt 7).getD i (0, 0)) ((rowsAt 10).getD i (0, 0)) := by
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

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Shared.Mixed.Gate08
