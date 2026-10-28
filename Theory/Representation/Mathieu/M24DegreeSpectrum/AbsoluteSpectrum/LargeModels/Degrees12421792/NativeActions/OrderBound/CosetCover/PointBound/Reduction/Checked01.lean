module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.OrderBound.CosetCover.PointBound.Reduction.Checked00

/-!
# Checked Tietze relations (block 1)

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

theorem h79 : eval g w79 = 1 := by
  exact substitution_relation g 0 replacement1 w41 w79 false 0
    (by decide +kernel) (eq1 g hi) (h41 g hi)

theorem h80 : eval g w80 = 1 := by
  exact substitution_relation g 0 replacement1 w45 w80 false 0
    (by decide +kernel) (eq1 g hi) (h45 g hi)

theorem h81 : eval g w81 = 1 := by
  exact substitution_relation g 0 replacement1 w46 w81 false 0
    (by decide +kernel) (eq1 g hi) (h46 g hi)

theorem h84 : eval g w84 = 1 := by
  exact substitution_relation g 0 replacement1 w54 w84 false 0
    (by decide +kernel) (eq1 g hi) (h54 g hi)

theorem h90 : eval g w90 = 1 := by
  exact substitution_relation g 2 replacement3 w68 w90 false 0
    (by decide +kernel) (eq3 g hi) (h68 g hi)

theorem h91 : eval g w91 = 1 := by
  exact substitution_relation g 2 replacement3 w3 w91 false 0
    (by decide +kernel) (eq3 g hi) (h3 g hi)

theorem h92 : eval g w92 = 1 := by
  exact substitution_relation g 2 replacement3 w69 w92 false 0
    (by decide +kernel) (eq3 g hi) (h69 g hi)

theorem h93 : eval g w93 = 1 := by
  exact substitution_relation g 2 replacement3 w70 w93 false 0
    (by decide +kernel) (eq3 g hi) (h70 g hi)

theorem h94 : eval g w94 = 1 := by
  exact substitution_relation g 2 replacement3 w71 w94 false 0
    (by decide +kernel) (eq3 g hi) (h71 g hi)

theorem h95 : eval g w95 = 1 := by
  exact substitution_relation g 2 replacement3 w72 w95 false 0
    (by decide +kernel) (eq3 g hi) (h72 g hi)

theorem h98 : eval g w98 = 1 := by
  exact substitution_relation g 2 replacement3 w79 w98 false 0
    (by decide +kernel) (eq3 g hi) (h79 g hi)

theorem h99 : eval g w99 = 1 := by
  exact substitution_relation g 2 replacement3 w81 w99 false 0
    (by decide +kernel) (eq3 g hi) (h81 g hi)

theorem h100 : eval g w100 = 1 := by
  exact substitution_relation g 2 replacement3 w52 w100 false 0
    (by decide +kernel) (eq3 g hi) (h52 g hi)

theorem h105 : eval g w105 = 1 := by
  exact substitution_relation g 3 replacement4 w90 w105 false 0
    (by decide +kernel) (eq4 g hi) (h90 g hi)

theorem h106 : eval g w106 = 1 := by
  exact substitution_relation g 3 replacement4 w92 w106 false 0
    (by decide +kernel) (eq4 g hi) (h92 g hi)

theorem h107 : eval g w107 = 1 := by
  exact substitution_relation g 3 replacement4 w93 w107 false 0
    (by decide +kernel) (eq4 g hi) (h93 g hi)

theorem h108 : eval g w108 = 1 := by
  exact substitution_relation g 3 replacement4 w94 w108 false 0
    (by decide +kernel) (eq4 g hi) (h94 g hi)

theorem h109 : eval g w109 = 1 := by
  exact substitution_relation g 3 replacement4 w95 w109 false 0
    (by decide +kernel) (eq4 g hi) (h95 g hi)

theorem h111 : eval g w111 = 1 := by
  exact substitution_relation g 3 replacement4 w74 w111 false 0
    (by decide +kernel) (eq4 g hi) (h74 g hi)

theorem h114 : eval g w114 = 1 := by
  exact substitution_relation g 3 replacement4 w77 w114 false 0
    (by decide +kernel) (eq4 g hi) (h77 g hi)

theorem h115 : eval g w115 = 1 := by
  exact substitution_relation g 3 replacement4 w78 w115 false 0
    (by decide +kernel) (eq4 g hi) (h78 g hi)

theorem h116 : eval g w116 = 1 := by
  exact substitution_relation g 3 replacement4 w98 w116 false 0
    (by decide +kernel) (eq4 g hi) (h98 g hi)

theorem h117 : eval g w117 = 1 := by
  exact substitution_relation g 3 replacement4 w80 w117 false 0
    (by decide +kernel) (eq4 g hi) (h80 g hi)

theorem h118 : eval g w118 = 1 := by
  exact substitution_relation g 3 replacement4 w99 w118 false 0
    (by decide +kernel) (eq4 g hi) (h99 g hi)

theorem h120 : eval g w120 = 1 := by
  exact substitution_relation g 3 replacement4 w100 w120 false 0
    (by decide +kernel) (eq4 g hi) (h100 g hi)

theorem h122 : eval g w122 = 1 := by
  exact substitution_relation g 3 replacement4 w84 w122 false 0
    (by decide +kernel) (eq4 g hi) (h84 g hi)

theorem h129 : eval g w129 = 1 := by
  exact substitution_relation g 4 replacement5 w105 w129 false 0
    (by decide +kernel) (eq5 g hi) (h105 g hi)

theorem h130 : eval g w130 = 1 := by
  exact substitution_relation g 4 replacement5 w106 w130 false 0
    (by decide +kernel) (eq5 g hi) (h106 g hi)

theorem h131 : eval g w131 = 1 := by
  exact substitution_relation g 4 replacement5 w107 w131 false 0
    (by decide +kernel) (eq5 g hi) (h107 g hi)

theorem h132 : eval g w132 = 1 := by
  exact substitution_relation g 4 replacement5 w108 w132 false 0
    (by decide +kernel) (eq5 g hi) (h108 g hi)

theorem h133 : eval g w133 = 1 := by
  exact substitution_relation g 4 replacement5 w109 w133 false 0
    (by decide +kernel) (eq5 g hi) (h109 g hi)

theorem h135 : eval g w135 = 1 := by
  exact substitution_relation g 4 replacement5 w116 w135 false 0
    (by decide +kernel) (eq5 g hi) (h116 g hi)

theorem h136 : eval g w136 = 1 := by
  exact substitution_relation g 4 replacement5 w118 w136 false 0
    (by decide +kernel) (eq5 g hi) (h118 g hi)

theorem h138 : eval g w138 = 1 := by
  exact substitution_relation g 4 replacement5 w120 w138 false 0
    (by decide +kernel) (eq5 g hi) (h120 g hi)

theorem h140 : eval g w140 = 1 := by
  exact substitution_relation g 4 replacement5 w122 w140 false 0
    (by decide +kernel) (eq5 g hi) (h122 g hi)

theorem h143 : eval g w143 = 1 := by
  exact substitution_relation g 4 replacement5 w64 w143 false 0
    (by decide +kernel) (eq5 g hi) (h64 g hi)

theorem h146 : eval g w146 = 1 := by
  exact substitution_relation g 6 replacement7 w129 w146 false 0
    (by decide +kernel) (eq7 g hi) (h129 g hi)

theorem h147 : eval g w147 = 1 := by
  exact substitution_relation g 6 replacement7 w91 w147 false 0
    (by decide +kernel) (eq7 g hi) (h91 g hi)

theorem h148 : eval g w148 = 1 := by
  exact substitution_relation g 6 replacement7 w132 w148 false 0
    (by decide +kernel) (eq7 g hi) (h132 g hi)

theorem h149 : eval g w149 = 1 := by
  exact substitution_relation g 6 replacement7 w9 w149 false 0
    (by decide +kernel) (eq7 g hi) (h9 g hi)

theorem h150 : eval g w150 = 1 := by
  exact substitution_relation g 6 replacement7 w133 w150 false 0
    (by decide +kernel) (eq7 g hi) (h133 g hi)

theorem h153 : eval g w153 = 1 := by
  exact substitution_relation g 6 replacement7 w17 w153 false 0
    (by decide +kernel) (eq7 g hi) (h17 g hi)

theorem h154 : eval g w154 = 1 := by
  exact substitution_relation g 6 replacement7 w27 w154 false 0
    (by decide +kernel) (eq7 g hi) (h27 g hi)

theorem h156 : eval g w156 = 1 := by
  exact substitution_relation g 6 replacement7 w115 w156 false 0
    (by decide +kernel) (eq7 g hi) (h115 g hi)

theorem h160 : eval g w160 = 1 := by
  exact substitution_relation g 6 replacement7 w138 w160 false 0
    (by decide +kernel) (eq7 g hi) (h138 g hi)

theorem h165 : eval g w165 = 1 := by
  exact substitution_relation g 7 replacement8 w146 w165 false 0
    (by decide +kernel) (eq8 g hi) (h146 g hi)

theorem h166 : eval g w166 = 1 := by
  exact substitution_relation g 7 replacement8 w147 w166 false 0
    (by decide +kernel) (eq8 g hi) (h147 g hi)

theorem h167 : eval g w167 = 1 := by
  exact substitution_relation g 7 replacement8 w148 w167 false 0
    (by decide +kernel) (eq8 g hi) (h148 g hi)

theorem h168 : eval g w168 = 1 := by
  exact substitution_relation g 7 replacement8 w149 w168 false 0
    (by decide +kernel) (eq8 g hi) (h149 g hi)

theorem h169 : eval g w169 = 1 := by
  exact substitution_relation g 7 replacement8 w150 w169 false 0
    (by decide +kernel) (eq8 g hi) (h150 g hi)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier.PointBound.Reduction
