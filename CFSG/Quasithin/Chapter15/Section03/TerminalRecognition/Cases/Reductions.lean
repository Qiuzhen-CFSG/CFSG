module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.SymmetricThreeGeneration
public import Stellmacher.ElementaryAbelianMaxGlobal

/-!
# Structural reductions in the terminal recognition cases

The S₃ branch is proved from an actual identification of the quotient
image of the elementary Thompson subgroup `X = J(G₀)`. The images of
`X_E` and `J(T_E)` do not commute, so they generate that S₃ image.
Since `Q₀ ≤ T_E`, this puts `X` in `X_E T_E`; relative normality and
residual perfection give `X_E = O²(X)`. Centralization by `Z` then
extends from the residual and the Sylow subgroup to `X`, and hence to
`F = ⟨Z^{Y_F}⟩` by the already proved conjugate-span lemma.

For the other branch, `Q₀ O₂(Y_F) ≤ R ≤ C(V)` and `[V,Q₁] = F ≠ 1`
give the strict inequality `O₂(Ȳ_F) < Q̇₁`. The two-cores, local
embeddings, and conjugation action are retained under quotient maps and
model equivalences. In particular, `V ≤ Q₀` does not mean that the
quotient action on `V` is trivial: the vectors belong to `V₀`, not to
the group quotient.

The F.6.18/B.5.6 intersection, the non-S₃ residual equality, and the
marked-model exclusions remain separate mathematical obligations. No
classification alternative is assumed in a record as a proof of them.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), printed p.1155, PDF p.1172.
-/

public section
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition
open Subgroup
variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
/-- The S₃ quotient image forces `X ≤ X_E T_E`, hence `X_E = O²(X)`. The auxiliary `J` is allowed to be `J(T_E)`. -/
theorem symmetricThree_residual (T : Sylow 2 H) (E J X : Subgroup H) [X.Normal]
    (hJX : J ≤ X) (hJT : J ≤ (T : Subgroup H))
    (hE : E = ⁅E,J⁆) (hEnot : ¬ E ≤ pCore 2 H)
    (hEp : IsPPerfect 2 E) (hTEn : (T : Subgroup H) ≤ normalizer (E : Set H))
    (e : (X.map (coreProjection (H := H))) ≃* Equiv.Perm (Fin 3)) :
    E = (pResidual 2 X).map X.subtype := by
  let q : H →* coreQuotient H := coreProjection
  have hEX : E ≤ X := hE.le.trans ((commutator_mono le_rfl hJX).trans
    (commutator_le_right _ _))
  let f : X →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp (q.subgroupMap X)
  have hk : f.ker = (pCore 2 H).subgroupOf X := by
    calc
      f.ker = (q.subgroupMap X).ker :=
        MonoidHom.ker_comp_of_injective (q.subgroupMap X) e.toMonoidHom e.injective
      _ = q.ker.subgroupOf X := Subgroup.ker_subgroupMap X q
      _ = (pCore 2 H).subgroupOf X := by
        rw [show q.ker = pCore 2 H from QuotientGroup.ker_mk' _]
  have hcomm : ⁅(E.subgroupOf X).map f, (J.subgroupOf X).map f⁆ ≠ ⊥ := by
    intro hc
    have hecomm : E.subgroupOf X = ⁅E.subgroupOf X, J.subgroupOf X⁆ := by
      apply (map_injective X.subtype_injective)
      rw [map_commutator, map_subgroupOf_eq_of_le hEX, map_subgroupOf_eq_of_le hJX]
      exact hE
    have hEf : (E.subgroupOf X).map f = ⊥ := by
      calc
        _ = (⁅E.subgroupOf X,J.subgroupOf X⁆).map f := congrArg (fun K => K.map f) hecomm
        _ = ⊥ := by rw [map_commutator]; exact hc
    have hEk := (Subgroup.map_eq_bot_iff _).mp hEf
    rw [hk] at hEk
    exact hEnot (fun x hx => hEk (show (⟨x,hEX hx⟩ : X) ∈ E.subgroupOf X from hx))
  have hgen := sup_eq_top_of_symmetricThree_commutator_ne_bot ((E.subgroupOf X).map f) ((J.subgroupOf X).map f) hcomm
  have hcover : (⊤ : Subgroup X) ≤ (E.subgroupOf X ⊔ J.subgroupOf X) ⊔
      (pCore 2 H).subgroupOf X := by
    rw [← hk, ← Subgroup.map_le_map_iff, Subgroup.map_sup, hgen]
    exact le_top
  have hXL : X ≤ E ⊔ (T : Subgroup H) := by
    have htop := map_mono (f := X.subtype) hcover
    rw [← MonoidHom.range_eq_map, range_subtype, Subgroup.map_sup, Subgroup.map_sup,
      map_subgroupOf_eq_of_le hEX, map_subgroupOf_eq_of_le hJX,
      subgroupOf_map_subtype] at htop
    exact htop.trans (sup_le (sup_le le_sup_left (hJT.trans le_sup_right))
      (inf_le_left.trans ((pCore_isPGroup.le_sylow_of_normal T).trans le_sup_right)))
  apply le_antisymm
  · have hp : IsPPerfect 2 (E.subgroupOf X) :=
      hEp.of_surjective (subgroupOfEquivOfLe hEX).symm.toMonoidHom
        (subgroupOfEquivOfLe hEX).symm.surjective
    have hl := map_mono (f := X.subtype)
      (le_pResidual_of_isPPerfect (E.subgroupOf X) hp)
    rwa [map_subgroupOf_eq_of_le hEX] at hl
  · exact (embedded_pResidual_mono 2 hXL).trans
      (embedded_pResidual_join_pGroup E T hEp T.isPGroup' hTEn).le
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition
open Subgroup
variable {H : Type*} [Group H] [Finite H]

/-- The actual quotient map carries a local two-core onto the two-core of its image. -/
theorem coreProjection_map_pCoreIn (Y : Subgroup H) :
    (Y.pCoreIn 2).map (coreProjection (H := H)) =
      (Y.map (coreProjection (H := H))).pCoreIn 2 := by
  apply map_pCoreIn_of_ker_isPGroup
  change IsPGroup 2 ((QuotientGroup.mk' (pCore 2 H)).ker)
  rw [QuotientGroup.ker_mk']
  exact pCore_isPGroup

/-- The source commutator `[V,Q₁] = F ≠ 1` forces `O₂(Ȳ_F) < Q̇₁`. -/
theorem localCore_strict (Y L V R F : Subgroup H)
    (hYL : Y ≤ L) (hn : L ≤ normalizer (Y : Set H))
    (hbound : pCore 2 H ⊔ Y.pCoreIn 2 ≤ R)
    (hR : R ≤ centralizer (V : Set H))
    (hcomm : ⁅V, L.pCoreIn 2⁆ = F) (hF : F ≠ ⊥) :
    (Y.map (coreProjection (H := H))).pCoreIn 2 <
      (L.map (coreProjection (H := H))).pCoreIn 2 := by
  rw [← coreProjection_map_pCoreIn, ← coreProjection_map_pCoreIn]
  refine lt_of_le_not_ge (map_mono (pCoreIn_mono_of_normalizes hYL hn)) ?_
  intro h
  have hle := Subgroup.map_le_map_iff.mp h
  have hk : (coreProjection (H := H)).ker = pCore 2 H := QuotientGroup.ker_mk' _
  rw [hk, sup_comm] at hle
  apply hF
  rw [← hcomm, commutator_eq_bot_iff_le_centralizer, le_centralizer_iff]
  exact hle.trans (hbound.trans hR)

open Representation.BinaryOffender Representation.NormalElementaryQuotient
variable (V : Subgroup H) [IsElementaryAbelian 2 (moduleClosure V)]
  (hC : IsPGroup 2 (centralizer (V : Set H)))
  (hcore : pCore 2 H ≤ centralizer (V : Set H))

omit [Finite H] in
/-- Pointwise fixation in the quotient representation is ambient centralization, even when the subgroup lies in the quotient kernel. -/
theorem quotientAction_fixedSpace_iff (P A : Subgroup H) (hP : P ≤ moduleClosure V) :
    planeSubspace V P ≤ fixedSpace (quotientAction V hC hcore) (A.map coreProjection) ↔
      P ≤ centralizer (A : Set H) := by
  constructor
  · intro h x hx
    let v : Additive (moduleClosure V) := Additive.ofMul ⟨x, hP hx⟩
    exact (mem_fixedSpace_image (moduleClosure V) coreProjection
      (QuotientGroup.mk'_surjective _) (coreProjection_ker V hC hcore) A v).mp
      (h (show v ∈ planeSubspace V P from hx))
  · intro h v hv
    apply (mem_fixedSpace_image (moduleClosure V) coreProjection
      (QuotientGroup.mk'_surjective _) (coreProjection_ker V hC hcore) A v).mpr
    exact h hv

/-- The image two-core of `Y_F` fixes the actual subspace `V` of `V₀`. -/
theorem localCore_fixes_subspace (Y R : Subgroup H)
    (hbound : pCore 2 H ⊔ Y.pCoreIn 2 ≤ R)
    (hR : R ≤ centralizer (V : Set H)) :
    planeSubspace V V ≤ fixedSpace (quotientAction V hC hcore)
      ((Y.map coreProjection).pCoreIn 2) := by
  rw [← coreProjection_map_pCoreIn]
  apply (quotientAction_fixedSpace_iff V hC hcore V (Y.pCoreIn 2) le_normalClosure).mpr
  exact le_centralizer_iff.mp (le_sup_right.trans (hbound.trans hR))
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition
open Subgroup
variable {H : Type*} [Group H] [Finite H]

/-- The actual elementary Thompson subgroup `X = J(G₀)`. -/
noncomputable abbrev thompsonGroup (H : Type*) [Group H] : Subgroup H :=
  Stellmacher.elementaryAbelianMaxJ ⊤

instance thompsonGroup_normal : (thompsonGroup H).Normal :=
  let _ := Stellmacher.elementaryAbelianMaxJ_top_characteristic (H := H)
  inferInstance

/-- The complete conditional S₃ branch, with `D = E`, `E = X_E`, and `Y = Y_F` in the source notation. No centralization of `X` is assumed. -/
theorem symmetricThree_branch (T : Sylow 2 H) (E D Z Y : Subgroup H)
    (hE : E = ⁅E, Stellmacher.elementaryAbelianMaxJ (T : Subgroup H)⁆)
    (hEnot : ¬ E ≤ pCore 2 H) (hEp : IsPPerfect 2 E)
    (hTEn : (T : Subgroup H) ≤ normalizer (E : Set H))
    (hZD : Z ≤ D) (hED : E ≤ centralizer (D : Set H))
    (hZT : Z ≤ centralizer (T : Set H))
    (e : ((thompsonGroup H).map coreProjection) ≃* Equiv.Perm (Fin 3)) :
    E = (pResidual 2 (thompsonGroup H)).map (thompsonGroup H).subtype ∧
      Z ≤ centralizer (thompsonGroup H : Set H) ∧
      conjugateSpanBy Z Y ≤ centralizer (thompsonGroup H : Set H) := by
  have hr := symmetricThree_residual T E (Stellmacher.elementaryAbelianMaxJ (T : Subgroup H))
    (thompsonGroup H) (Stellmacher.elementaryAbelianMaxJ_sylow_le_top T)
    (sSup_le fun _ hA => hA.1) hE hEnot hEp hTEn e
  have hZE : Z ≤ centralizer (E : Set H) := hZD.trans (le_centralizer_iff.mp hED)
  have hZX := centralizes_normal_of_centralizes_pResidual_and_sylow T (thompsonGroup H) Z
    (hr ▸ hZE) hZT
  exact ⟨hr, hZX, conjugateSpan_centralizes_normal Z Y (thompsonGroup H) hZX⟩

omit [Finite H] in
/-- Equality of the embedded residuals puts every two-perfect subgroup of `G₀` in `X`. -/
theorem perfect_le_of_residual_eq (X Y : Subgroup H)
    (hY : IsPPerfect 2 Y)
    (hres : (pResidual 2 X).map X.subtype = pResidual 2 H) : Y ≤ X :=
  (le_pResidual_of_isPPerfect Y hY).trans (hres ▸ map_subtype_le (pResidual 2 X))
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition
open Subgroup
variable {H : Type*} [Group H]

/-- The non-S₃ residual identity yields both `Y_F ≤ X` and the required commutator identity on the normal closure. -/
theorem moduleClosure_eq_commutator_of_residual_eq (V X Y : Subgroup H) [X.Normal]
    (hY : IsPPerfect 2 Y)
    (hres : (pResidual 2 X).map X.subtype = pResidual 2 H)
    (hV : V = ⁅V,Y⁆) : moduleClosure V = ⁅moduleClosure V,X⁆ :=
  moduleClosure_eq_commutator V X Y (perfect_le_of_residual_eq X Y hY hres) hV

variable [Finite H]
/-- The strict local-core inequality survives a connected group identification; both local embeddings are transported through the same equivalence. -/
theorem localCore_strict_in_model (Y L V R F : Subgroup H)
    (hYL : Y ≤ L) (hn : L ≤ normalizer (Y : Set H))
    (hbound : pCore 2 H ⊔ Y.pCoreIn 2 ≤ R)
    (hR : R ≤ centralizer (V : Set H))
    (hcomm : ⁅V, L.pCoreIn 2⁆ = F) (hF : F ≠ ⊥)
    {K : Type*} [Group K] (e : coreQuotient H ≃* K) :
    (Y.map (e.toMonoidHom.comp coreProjection)).pCoreIn 2 <
      (L.map (e.toMonoidHom.comp coreProjection)).pCoreIn 2 := by
  let _ : Finite K := Finite.of_equiv (coreQuotient H) e.toEquiv
  have hk : IsPGroup 2 e.toMonoidHom.ker :=
    IsPGroup.ker_isPGroup_of_injective e.injective
  have hs := (Subgroup.map_lt_map_iff_of_injective (f := e.toMonoidHom) e.injective).mpr
    (localCore_strict Y L V R F hYL hn hbound hR hcomm hF)
  rw [map_pCoreIn_of_ker_isPGroup e.toMonoidHom hk, map_pCoreIn_of_ker_isPGroup e.toMonoidHom hk,
    map_map, map_map] at hs
  exact hs
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition
