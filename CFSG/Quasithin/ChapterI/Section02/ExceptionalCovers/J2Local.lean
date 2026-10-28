module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.Definitions
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.J2Local.Restriction
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.J2Local.QuotientOrbit
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.J2Local.ModuleSplitting

/-!
# The local double cover of the marked J₂ centralizer

The literal centralizer's perfection and square-root orbit construct a
nonidentity involution square in its preimage under the original central
quotient. The checked radical generators make the two-core modulo that square
elementary abelian. Its actual A₅ module is projective, giving a central
complement to the intrinsic commutator and identifying the quotient by that
commutator with SL₂(5), compatibly with the original five-point action.

`centralizer_structure` identifies this same preimage with both `C_K(u)` and
`O²(C_K(u))` for every lift of the marking. The ambient square equality,
commutator quotient, central supplement and involution exclusion therefore
apply to the source's literal residual and two-core, with no abstract local
model substitution. The square-lifting and unique-square endpoints from
`QuotientOrbit` are re-exported here.

Only the earlier source inputs `|Z(K)| = 2` and the central-cover restriction
law (i), `Z(K) ≤ [H,H]`, remain explicit. Perfection, the square-root orbit,
elementary structure, projectivity, splitting and recognition are discharged.
Global conjugacy transport, outer inversion and the full I.2.2 statement remain
with the exceptional-cover assembly.

Source: Aschbacher–Smith, I.2.2(5), printed pp.411–412 / PDF pp.422–423
(combined manuscript of 1 March 2004).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.J2Local
open Sporadic.LeechRelated.J2
open ExceptionalParabolics.Seed ExceptionalParabolics.FirstParabolic
variable {K : Type*} [Group K] [Finite K]
variable (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
variable (hi : center K ≤ ⁅preimage e, preimage e⁆)

/-- The distinguished square in the literal local cover, with all local
perfection and orbit inputs discharged. -/
noncomputable def localSquare : preimage e := by
  let := preimage_isPerfect e hi
  exact distinguishedSquare e hZ
    CoverSquareOrbit.exists_core_square CoverSquareOrbit.core_square_isConj

/-- The square is a nonidentity involution over the marked quotient element,
and is the only square in the two-core above that element. -/
theorem localSquare_spec :
    orderOf (localSquare e hZ hi) = 2 ∧
    restriction e (localSquare e hZ hi) = marked ∧
    (∃ x ∈ pCore 2 (preimage e), x ^ 2 = localSquare e hZ hi) ∧
    ∀ w : preimage e, restriction e w = marked →
      (∃ x ∈ pCore 2 (preimage e), x ^ 2 = w) → w = localSquare e hZ hi := by
  let := preimage_isPerfect e hi
  exact distinguishedSquare_spec e hZ
    CoverSquareOrbit.exists_core_square CoverSquareOrbit.core_square_isConj

theorem localSquare_central : localSquare e hZ hi ∈ center (preimage e) := by
  let := preimage_isPerfect e hi
  exact distinguishedSquare_central e hZ
    CoverSquareOrbit.exists_core_square CoverSquareOrbit.core_square_isConj

instance localSquare_zpowers_normal : (zpowers (localSquare e hZ hi)).Normal where
  conj_mem x hx g := by
    have hc := (zpowers_le.mpr (localSquare_central e hZ hi)) hx
    rw [mem_center_iff.mp hc g]
    simpa using hx

include hi in
/-- The actual centralizer, its two-residual, and its embedded two-core. -/
theorem centralizer_structure (u : K) (hu : projection e u = z) :
    centralizer ({u} : Set K) = preimage e ∧
    centralizerTwoResidual u = preimage e ∧
    centralizerCore u = (pCore 2 (preimage e)).map (preimage e).subtype := by
  let := preimage_isPerfect e hi
  exact ⟨centralizer_eq_preimage e u hu, residual_eq_preimage e u hu,
    core_eq_preimage_core e u hu⟩

/-- The source quotient `R/⟨v⟩`, formed inside the literal local preimage,
is elementary abelian. -/
theorem core_quotient_elementary_of_restriction :
    IsElementaryAbelian 2 ((pCore 2 (preimage e)) ⧸
      (zpowers (localSquare e hZ hi)).subgroupOf (pCore 2 (preimage e))) := by
  let := preimage_isPerfect e hi
  exact core_quotient_elementary e hZ
    CoverSquareOrbit.exists_core_square CoverSquareOrbit.core_square_isConj

include hZ hi in
/-- Projectivity splits off the original covering center from `[R,X]`.
Both factors are subgroups of the actual local preimage. -/
theorem core_central_complement_of_restriction :
    pCore 2 (preimage e) =
      coreCommutator e ⊔ (center K).subgroupOf (preimage e) ∧
    Disjoint (coreCommutator e) ((center K).subgroupOf (preimage e)) := by
  let := preimage_isPerfect e hi
  exact core_central_complement e hZ
    CoverSquareOrbit.exists_core_square CoverSquareOrbit.core_square_isConj

include hZ hi in
/-- The SL₂(5) recognition commutes with the literal five-point A₅ action.
In particular, the local preimage has no involutions outside its two-core. -/
theorem commutator_quotient_of_restriction :
    (∃ d : ((preimage e) ⧸ coreCommutator e) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod 5),
      (GorensteinWalter.AlternatingFiveDoubleCover.projection.comp d.toMonoidHom).comp
        (QuotientGroup.mk' (coreCommutator e)) = a5Action e) ∧
    (∀ x : preimage e, orderOf x = 2 → x ∈ pCore 2 (preimage e)) := by
  let := preimage_isPerfect e hi
  exact commutator_quotient_of_quotient_orbit e hZ
    CoverSquareOrbit.exists_core_square CoverSquareOrbit.core_square_isConj

/-- Equality of all squares in the literal residual core which map to the
marked involution; the result is an equality in the original covering group. -/
theorem core_square_eq (u : K) (hu : projection e u = z)
    (x : K) (hx : x ∈ centralizerCore u) (hx2 : projection e (x ^ 2) = z) :
    x ^ 2 = (localSquare e hZ hi : K) := by
  rw [(centralizer_structure e hi u hu).2.2] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy2 : restriction e (y ^ 2) = marked := by
    apply Subtype.ext
    change projection e ((preimage e).subtype (y ^ 2)) = z
    simpa only [map_pow] using hx2
  exact congrArg (fun a : preimage e => (a : K))
    ((localSquare_spec e hZ hi).2.2.2 (y ^ 2) hy2 ⟨y, hy, rfl⟩)

/-- The distinguished involution is a square in `O₂(O²(C_K(u)))`,
using the original central quotient map rather than an abstract local model. -/
theorem localSquare_ambient_spec (u : K) (hu : projection e u = z) :
    orderOf (localSquare e hZ hi : K) = 2 ∧
    projection e (localSquare e hZ hi : K) = z ∧
    (∃ x ∈ centralizerCore u, x ^ 2 = (localSquare e hZ hi : K)) ∧
    QuotientGroup.mk' (center K) (localSquare e hZ hi : K) =
      QuotientGroup.mk' (center K) u := by
  obtain ⟨hv, hp, ⟨x, hx, hs⟩, _⟩ := localSquare_spec e hZ hi
  have hproj : projection e (localSquare e hZ hi : K) = z := congrArg Subtype.val hp
  refine ⟨?_, hproj, ⟨x.val, ?_, congrArg Subtype.val hs⟩, ?_⟩
  · exact (orderOf_injective (preimage e).subtype
      (preimage e).subtype_injective _).trans hv
  · rw [(centralizer_structure e hi u hu).2.2]
    exact ⟨x, hx, rfl⟩
  · exact e.injective (hproj.trans hu.symm)

include hZ hi in
/-- The source's involution exclusion on the literal two-residual. -/
theorem residual_involution_mem_core (u : K) (hu : projection e u = z)
    (x : K) (hx : x ∈ centralizerTwoResidual u) (hx2 : orderOf x = 2) :
    x ∈ centralizerCore u := by
  have hstr := centralizer_structure e hi u hu
  rw [hstr.2.1] at hx
  rw [hstr.2.2]
  refine ⟨⟨x, hx⟩, ?_, rfl⟩
  apply (commutator_quotient_of_restriction e hZ hi).2
  exact (orderOf_injective (preimage e).subtype
    (preimage e).subtype_injective ⟨x, hx⟩).symm.trans hx2

include hZ hi in
/-- The abstract recognition applies to exactly `X/[O₂(X),X]`, where
`X = O²(C_K(u))`, as required by the source. The compatible projection to A₅
is supplied by `commutator_quotient_of_restriction` and `centralizer_structure`. -/
theorem residual_commutator_quotient (u : K) (hu : projection e u = z) :
    Nonempty (((centralizerTwoResidual u) ⧸
      ⁅pCore 2 (centralizerTwoResidual u), (⊤ : Subgroup (centralizerTwoResidual u))⁆) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) := by
  rw [(centralizer_structure e hi u hu).2.1]
  obtain ⟨d, _⟩ := (commutator_quotient_of_restriction e hZ hi).1
  exact ⟨d⟩

include hZ hi in
/-- The source equality `R = [R,X]Z`, with the residual, its commutator,
and the original covering center all embedded in `K`. -/
theorem residual_core_central_supplement (u : K) (hu : projection e u = z) :
    centralizerCore u =
      (⁅pCore 2 (centralizerTwoResidual u),
        (⊤ : Subgroup (centralizerTwoResidual u))⁆).map
          (centralizerTwoResidual u).subtype ⊔ center K := by
  rw [centralizerCore, (centralizer_structure e hi u hu).2.1]
  calc
    _ = (coreCommutator e ⊔ (center K).subgroupOf (preimage e)).map
        (preimage e).subtype :=
      congrArg (Subgroup.map (preimage e).subtype)
        (core_central_complement_of_restriction e hZ hi).1
    _ = _ := by rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (center_le_preimage e)]

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.J2Local
