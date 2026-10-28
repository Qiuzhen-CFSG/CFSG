module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.CosetCover.PointBound.Reduction.Checked01

/-!
# Checked Tietze relations (block 2)

Every input is read from the literal point Schreier presentation. Explicit
intermediate words prevent recursive reconstruction of the discovery trace.
See `../source/README.md` for the deterministic, untrusted producer.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier.PointBound.Reduction
open Subgroup.CosetWordCertificate
variable {G : Type*} [Group G] (g : Nat → G)
  (hi : ∀ r, eval g (inputWord r) = 1)
include hi

theorem h171 : eval g w171 = 1 := by
  exact substitution_relation g 7 replacement8 w153 w171 false 0
    (by decide +kernel) (eq8 g hi) (h153 g hi)

theorem h173 : eval g w173 = 1 := by
  exact substitution_relation g 7 replacement8 w154 w173 false 0
    (by decide +kernel) (eq8 g hi) (h154 g hi)

theorem h175 : eval g w175 = 1 := by
  exact substitution_relation g 7 replacement8 w156 w175 false 0
    (by decide +kernel) (eq8 g hi) (h156 g hi)

theorem h176 : eval g w176 = 1 := by
  exact substitution_relation g 7 replacement8 w135 w176 false 0
    (by decide +kernel) (eq8 g hi) (h135 g hi)

theorem h180 : eval g w180 = 1 := by
  exact substitution_relation g 7 replacement8 w160 w180 false 0
    (by decide +kernel) (eq8 g hi) (h160 g hi)

theorem h185 : eval g w185 = 1 := by
  exact substitution_relation g 9 replacement10 w165 w185 false 0
    (by decide +kernel) (eq10 g hi) (h165 g hi)

theorem h186 : eval g w186 = 1 := by
  exact substitution_relation g 9 replacement10 w166 w186 false 0
    (by decide +kernel) (eq10 g hi) (h166 g hi)

theorem h187 : eval g w187 = 1 := by
  exact substitution_relation g 9 replacement10 w130 w187 false 0
    (by decide +kernel) (eq10 g hi) (h130 g hi)

theorem h188 : eval g w188 = 1 := by
  exact substitution_relation g 9 replacement10 w131 w188 false 0
    (by decide +kernel) (eq10 g hi) (h131 g hi)

theorem h189 : eval g w189 = 1 := by
  exact substitution_relation g 9 replacement10 w167 w189 false 0
    (by decide +kernel) (eq10 g hi) (h167 g hi)

theorem h190 : eval g w190 = 1 := by
  exact substitution_relation g 9 replacement10 w169 w190 false 0
    (by decide +kernel) (eq10 g hi) (h169 g hi)

theorem h192 : eval g w192 = 1 := by
  exact substitution_relation g 9 replacement10 w111 w192 false 0
    (by decide +kernel) (eq10 g hi) (h111 g hi)

theorem h193 : eval g w193 = 1 := by
  exact substitution_relation g 9 replacement10 w171 w193 false 0
    (by decide +kernel) (eq10 g hi) (h171 g hi)

theorem h195 : eval g w195 = 1 := by
  exact substitution_relation g 9 replacement10 w173 w195 false 0
    (by decide +kernel) (eq10 g hi) (h173 g hi)

theorem h197 : eval g w197 = 1 := by
  exact substitution_relation g 9 replacement10 w114 w197 false 0
    (by decide +kernel) (eq10 g hi) (h114 g hi)

theorem h199 : eval g w199 = 1 := by
  exact substitution_relation g 9 replacement10 w175 w199 false 0
    (by decide +kernel) (eq10 g hi) (h175 g hi)

theorem h200 : eval g w200 = 1 := by
  exact substitution_relation g 9 replacement10 w117 w200 false 0
    (by decide +kernel) (eq10 g hi) (h117 g hi)

theorem h201 : eval g w201 = 1 := by
  exact substitution_relation g 9 replacement10 w136 w201 false 0
    (by decide +kernel) (eq10 g hi) (h136 g hi)

theorem h205 : eval g w205 = 1 := by
  exact substitution_relation g 9 replacement10 w180 w205 false 0
    (by decide +kernel) (eq10 g hi) (h180 g hi)

theorem h207 : eval g w207 = 1 := by
  exact substitution_relation g 9 replacement10 w140 w207 false 0
    (by decide +kernel) (eq10 g hi) (h140 g hi)

theorem h213 : eval g w213 = 1 := by
  exact substitution_relation g 10 replacement11 w185 w213 false 0
    (by decide +kernel) (eq11 g hi) (h185 g hi)

theorem h214 : eval g w214 = 1 := by
  exact substitution_relation g 10 replacement11 w186 w214 false 0
    (by decide +kernel) (eq11 g hi) (h186 g hi)

theorem h215 : eval g w215 = 1 := by
  exact substitution_relation g 10 replacement11 w187 w215 false 0
    (by decide +kernel) (eq11 g hi) (h187 g hi)

theorem h216 : eval g w216 = 1 := by
  exact substitution_relation g 10 replacement11 w189 w216 false 0
    (by decide +kernel) (eq11 g hi) (h189 g hi)

theorem h217 : eval g w217 = 1 := by
  exact substitution_relation g 10 replacement11 w168 w217 false 0
    (by decide +kernel) (eq11 g hi) (h168 g hi)

theorem h221 : eval g w221 = 1 := by
  exact substitution_relation g 10 replacement11 w193 w221 false 0
    (by decide +kernel) (eq11 g hi) (h193 g hi)

theorem h224 : eval g w224 = 1 := by
  exact substitution_relation g 10 replacement11 w22 w224 false 0
    (by decide +kernel) (eq11 g hi) (h22 g hi)

theorem h229 : eval g w229 = 1 := by
  exact substitution_relation g 10 replacement11 w200 w229 false 0
    (by decide +kernel) (eq11 g hi) (h200 g hi)

theorem h233 : eval g w233 = 1 := by
  exact substitution_relation g 11 replacement12 w213 w233 false 0
    (by decide +kernel) (eq12 g hi) (h213 g hi)

theorem h234 : eval g w234 = 1 := by
  exact substitution_relation g 11 replacement12 w188 w234 false 0
    (by decide +kernel) (eq12 g hi) (h188 g hi)

theorem h235 : eval g w235 = 1 := by
  exact substitution_relation g 11 replacement12 w216 w235 false 0
    (by decide +kernel) (eq12 g hi) (h216 g hi)

theorem h236 : eval g w236 = 1 := by
  exact substitution_relation g 11 replacement12 w217 w236 false 0
    (by decide +kernel) (eq12 g hi) (h217 g hi)

theorem h240 : eval g w240 = 1 := by
  exact substitution_relation g 11 replacement12 w192 w240 false 0
    (by decide +kernel) (eq12 g hi) (h192 g hi)

theorem h241 : eval g w241 = 1 := by
  exact substitution_relation g 11 replacement12 w221 w241 false 0
    (by decide +kernel) (eq12 g hi) (h221 g hi)

theorem h244 : eval g w244 = 1 := by
  exact substitution_relation g 11 replacement12 w224 w244 false 0
    (by decide +kernel) (eq12 g hi) (h224 g hi)

theorem h248 : eval g w248 = 1 := by
  exact substitution_relation g 11 replacement12 w197 w248 false 0
    (by decide +kernel) (eq12 g hi) (h197 g hi)

theorem h251 : eval g w251 = 1 := by
  exact substitution_relation g 11 replacement12 w229 w251 false 0
    (by decide +kernel) (eq12 g hi) (h229 g hi)

theorem h252 : eval g w252 = 1 := by
  exact substitution_relation g 11 replacement12 w201 w252 false 0
    (by decide +kernel) (eq12 g hi) (h201 g hi)

theorem h256 : eval g w256 = 1 := by
  exact substitution_relation g 11 replacement12 w207 w256 false 0
    (by decide +kernel) (eq12 g hi) (h207 g hi)

theorem h262 : eval g w262 = 1 := by
  exact substitution_relation g 12 replacement13 w233 w262 false 0
    (by decide +kernel) (eq13 g hi) (h233 g hi)

theorem h263 : eval g w263 = 1 := by
  exact substitution_relation g 12 replacement13 w235 w263 false 0
    (by decide +kernel) (eq13 g hi) (h235 g hi)

theorem h264 : eval g w264 = 1 := by
  exact substitution_relation g 12 replacement13 w236 w264 false 0
    (by decide +kernel) (eq13 g hi) (h236 g hi)

theorem h266 : eval g w266 = 1 := by
  exact substitution_relation g 12 replacement13 w190 w266 false 0
    (by decide +kernel) (eq13 g hi) (h190 g hi)

theorem h269 : eval g w269 = 1 := by
  exact substitution_relation g 12 replacement13 w241 w269 false 0
    (by decide +kernel) (eq13 g hi) (h241 g hi)

theorem h272 : eval g w272 = 1 := by
  exact substitution_relation g 12 replacement13 w244 w272 false 0
    (by decide +kernel) (eq13 g hi) (h244 g hi)

theorem h274 : eval g w274 = 1 := by
  exact substitution_relation g 12 replacement13 w195 w274 false 0
    (by decide +kernel) (eq13 g hi) (h195 g hi)

theorem h278 : eval g w278 = 1 := by
  exact substitution_relation g 12 replacement13 w199 w278 false 0
    (by decide +kernel) (eq13 g hi) (h199 g hi)

theorem h279 : eval g w279 = 1 := by
  exact substitution_relation g 12 replacement13 w251 w279 false 0
    (by decide +kernel) (eq13 g hi) (h251 g hi)

theorem h282 : eval g w282 = 1 := by
  exact substitution_relation g 12 replacement13 w205 w282 false 0
    (by decide +kernel) (eq13 g hi) (h205 g hi)

theorem h286 : eval g w286 = 1 := by
  exact substitution_relation g 13 replacement14 w262 w286 false 0
    (by decide +kernel) (eq14 g hi) (h262 g hi)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier.PointBound.Reduction
