module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.Geometry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FixedCodimensions.Source
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.CommonNormalKnownSimple
public import Theory.GroupTheory.TwoLocalUniquenessControl

/-!
# Hyperplane centralizers through the actual natural quotient

The original projection identifies hyperplanes containing C_V(L) with binary
hyperplanes of the marked quotient, preserving index and actual L-conjugacy.
The Sylow action on that quotient fixes a dual vector, producing an invariant
hyperplane. The proved E.6.13 theorem controls its ambient centralizer; natural
hyperplane transitivity controls all other hyperplanes containing the kernel.
This proves the parameter lower bound whenever C_V(L)=1.

With the earlier source uniqueness over L, any remaining escaping hyperplane
meets C_V(L) trivially. Its binary index then forces the central kernel to have
order two and the hyperplane to complement it. The resulting lower-bound
consumer covers every other kernel order. The order-two nonsplit case remains
with qt-d-1222-natural-weak-parameters; its orthogonal complement and E.6.14
argument are not assumed here. The permitted earlier TI and uniqueness inputs
retain their original preliminary and normalizer producers, and the parent
qt-d-1222-natural-weak-closure-source owns final source assembly.

Source: Aschbacher--Smith, 11.2.2, printed pp.767--768, using E.6.13,
printed p.250, and source 4.2.13 uniqueness over L.
-/

public noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterE
open CFSG.Quasithin.ChapterE.Section06
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (c : Coordinates D S.field)
include D S c

private def binaryPullback (Q : Submodule (ZMod 2) c.Space) : Subgroup G :=
  (Q.toAddSubgroup.toSubgroup.comap c.projection).map V.subtype

private theorem mem_binaryPullback (Q : Submodule (ZMod 2) c.Space) (v : V) :
    (v : G) ∈ binaryPullback D S c Q ↔ (c.projection v).toAdd ∈ Q := by
  constructor
  · rintro ⟨w,hw,he⟩
    exact V.subtype_injective he ▸ hw
  · intro hv
    exact ⟨v,hv,rfl⟩

private theorem binaryPullback_le (Q : Submodule (ZMod 2) c.Space) :
    binaryPullback D S c Q ≤ V := map_subtype_le _

private theorem binaryPullback_corank (Q : Submodule (ZMod 2) c.Space) :
    subgroupCorank V (binaryPullback D S c Q) =
      Module.finrank (ZMod 2) (c.Space ⧸ Q) := by
  let : Finite c.Space := Finite.of_surjective c.projection c.projection_surjective
  have he : (binaryPullback D S c Q).subgroupOf V =
      Q.toAddSubgroup.toSubgroup.comap c.projection := by
    ext v
    exact mem_binaryPullback D S c Q v
  rw [subgroupCorank,Subgroup.relIndex,he,
    Subgroup.index_comap_of_surjective _ c.projection_surjective,
    AddSubgroup.index_toSubgroup,AddSubgroup.index_eq_card]
  change Nat.log 2 (Nat.card (c.Space ⧸ Q)) = _
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
    Nat.log_pow (by decide : 1 < 2)]

private theorem exists_binaryPullback {U : Subgroup G} (hUV : U ≤ V)
    (hker : V ⊓ centralizer (L : Set G) ≤ U) :
    ∃ Q : Submodule (ZMod 2) c.Space, binaryPullback D S c Q = U := by
  let Q : Submodule (ZMod 2) c.Space := AddSubgroup.toZModSubmodule 2
    ((U.subgroupOf V).map c.projection).toAddSubgroup'
  refine ⟨Q,le_antisymm ?_ ?_⟩
  · rintro x ⟨v,hv,rfl⟩
    obtain ⟨w,hw,he⟩ : ∃ w : V, w ∈ U.subgroupOf V ∧ c.projection w = c.projection v := hv
    have hk : (w⁻¹ * v : V) ∈ c.projection.ker := by
      change c.projection (w⁻¹ * v) = 1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    have hc : ((w⁻¹ * v : V) : G) ∈ U :=
      hker ⟨(w⁻¹ * v).property,(c.projection_eq_one_iff _).mp hk⟩
    have hh := U.mul_mem hw hc
    simpa using hh
  · intro x hx
    refine ⟨⟨x,hUV hx⟩,?_,rfl⟩
    exact ⟨⟨x,hUV hx⟩,hx,rfl⟩

private theorem binaryPullback_conjugate (Q : Submodule (ZMod 2) c.Space) (l : L) :
    (binaryPullback D S c Q).map (MulAut.conj (l : G)).toMonoidHom =
      binaryPullback D S c (Q.map ((c.modelAction (c.quotientMap l)).restrictScalars (ZMod 2))) := by
  apply le_antisymm
  · rintro x ⟨v,hv,rfl⟩
    let v' : V := ⟨v,binaryPullback_le D S c Q hv⟩
    let w := V.normalizerMonoidHom (inclusion D.normalizes l) v'
    apply (mem_binaryPullback D S c _ w).mpr
    rw [c.projection_component_conjugation]
    exact ⟨(c.projection v').toAdd,(mem_binaryPullback D S c Q v').mp hv,rfl⟩
  · intro x hx
    let v : V := ⟨x,binaryPullback_le D S c _ hx⟩
    obtain ⟨q,hq,hqv⟩ := (mem_binaryPullback D S c _ v).mp hx
    let w := V.normalizerMonoidHom (inclusion D.normalizes l⁻¹) v
    have hw : (w : G) ∈ binaryPullback D S c Q := by
      apply (mem_binaryPullback D S c Q w).mpr
      rw [c.projection_component_conjugation, map_inv, ←hqv]
      change c.modelAction (c.quotientMap l)⁻¹ (c.modelAction (c.quotientMap l) q) ∈ Q
      rw [c.modelAction.inv_self_apply]
      exact hq
    refine ⟨w,hw,?_⟩
    change (l:G) * ((l:G)⁻¹ * x * ((l:G)⁻¹)⁻¹) * (l:G)⁻¹ = x
    group

private theorem quotient_hyperplanes_transitive
    (Q R : Submodule (ZMod 2) c.Space)
    (hQ : Module.finrank (ZMod 2) Q + 1 = Module.finrank (ZMod 2) c.Space)
    (hR : Module.finrank (ZMod 2) R + 1 = Module.finrank (ZMod 2) c.Space) :
    ∃ a : c.ModelGroup, Q.map ((c.modelAction a).restrictScalars (ZMod 2)) = R := by
  cases c with
  | sl3 m => exact sl3_binary_hyperplanes Q R hQ hR
  | sp4 m => exact sp4_binary_hyperplanes Q R hQ hR
  | g2 m => exact g2_binary_hyperplanes Q R hQ hR

/-- Every binary hyperplane containing C_V(L) is an actual L-conjugate
of every other such hyperplane. -/
theorem hyperplanes_containing_kernel_conjugate {U W : Subgroup G}
    (hUV : U ≤ V) (hWV : W ≤ V)
    (hCU : V ⊓ centralizer (L : Set G) ≤ U)
    (hCW : V ⊓ centralizer (L : Set G) ≤ W)
    (hU : subgroupCorank V U = 1) (hW : subgroupCorank V W = 1) :
    ∃ l : L, U.map (MulAut.conj (l : G)).toMonoidHom = W := by
  let : Finite c.Space := Finite.of_surjective c.projection c.projection_surjective
  obtain ⟨Q,rfl⟩ := exists_binaryPullback D S c hUV hCU
  obtain ⟨R,rfl⟩ := exists_binaryPullback D S c hWV hCW
  rw [binaryPullback_corank D S c] at hU hW
  have hdQ := Submodule.finrank_quotient_add_finrank Q
  have hdR := Submodule.finrank_quotient_add_finrank R
  obtain ⟨a,ha⟩ := quotient_hyperplanes_transitive D S c Q R (by omega) (by omega)
  obtain ⟨l,hl⟩ := c.quotientMap_surjective a
  refine ⟨l,?_⟩
  rw [binaryPullback_conjugate D S c,hl,ha]

private theorem exists_normal_hyperplane_containing_kernel :
    ∃ W : Subgroup G, W ≤ V ∧ subgroupCorank V W = 1 ∧
      V ⊓ centralizer (L : Set G) ≤ W ∧
      (W.subgroupOf (T : Subgroup G)).Normal := by
  let := D.elementary
  let : Finite c.Space := Finite.of_surjective c.projection c.projection_surjective
  have hd := NaturalDimensions.field_dimension D S c
  let : Nontrivial c.Space := Module.nontrivial_of_finrank_pos (R := S.field.Carrier)
    (by cases c <;> simp_all)
  obtain ⟨ρ,hρ,he,hres⟩ := FullAutomizer.exists_faithful_quotient_action D S c
  let q : T →* Automizer V :=
    V.normalizerMonoidHom.rangeRestrict.comp (inclusion S.sylow_normalizes)
  obtain ⟨Q,hQ,hfix⟩ := Representation.exists_invariant_binary_hyperplane (ρ.comp q) T.isPGroup'
  let W := binaryPullback D S c Q
  have hWV : W ≤ V := binaryPullback_le D S c Q
  refine ⟨W,hWV,?_,?_,?_⟩
  · rw [binaryPullback_corank D S c]
    have := Submodule.finrank_quotient_add_finrank Q
    omega
  · intro v hv
    apply (mem_binaryPullback D S c Q ⟨v,hv.1⟩).mpr
    rw [(c.projection_eq_one_iff _).mpr hv.2]
    exact Q.zero_mem
  · apply (normal_subgroupOf_iff_le_normalizer (hWV.trans D.le_sylow)).mpr
    apply le_normalizer_iff.mpr
    intro t ht w hw
    let v : V := ⟨w,hWV hw⟩
    let v' := V.normalizerMonoidHom (inclusion S.sylow_normalizes ⟨t,ht⟩) v
    apply (mem_binaryPullback D S c Q v').mpr
    have he' := he (q ⟨t,ht⟩) (Additive.ofMul v)
    change (c.projection v').toAdd = ρ (q ⟨t,ht⟩) (c.projection v).toAdd at he'
    rw [he']
    exact hfix ⟨t,ht⟩ _ ((mem_binaryPullback D S c Q v).mp hw)

/-- E.6.13 controls every hyperplane containing the full central kernel.
The full original seed and the actual ambient normalizer are retained. -/
theorem centralizer_le_of_kernel_le
    (hE : HypothesisE61 KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V)
    {U : Subgroup G} (hUV : U ≤ V) (hU : subgroupCorank V U = 1)
    (hCU : V ⊓ centralizer (L : Set G) ≤ U) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) := by
  let := D.elementary
  obtain ⟨W,hWV,hW,hCW,hWT⟩ := exists_normal_hyperplane_containing_kernel D S c
  have hm := localM_eq_naturalParameter D S c
  have hsmall : subgroupCorank V W < localM V := by
    rw [hW,hm]
    exact naturalParameter_gt_one D S c
  have hWC := InvariantSubspaces.centralizer_le_of_normal_in_sylow_knownSimple hE
    (nontrivial_of_corank_lt_localM hsmall) hWV
    (hE.oddCentralizerCondition_of_small hWV hsmall) hWT
  obtain ⟨l,hl⟩ := hyperplanes_containing_kernel_conjugate D S c hUV hWV hCU hCW hU hW
  intro x hx
  have hx' : (l:G)*x*(l:G)⁻¹ ∈ centralizer (W : Set G) := by
    rw [←hl]
    exact map_centralizer_le_centralizer_image (U : Set G) (MulAut.conj (l:G)).toMonoidHom
      (mem_map_of_mem _ hx)
  have hlM : (l:G) ∈ normalizer (L : Set G) := L.le_normalizer l.property
  have hh := (normalizer (L : Set G)).mul_mem
    ((normalizer (L : Set G)).mul_mem ((normalizer (L : Set G)).inv_mem hlM) (hWC hx')) hlM
  simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel_right,inv_mul_cancel,mul_one] using hh

/-- All binary hyperplane centralizers are controlled when the original
central kernel vanishes; the field degree and marking are unrestricted. -/
theorem centralizer_le_of_central_kernel_eq_bot
    (hE : HypothesisE61 KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V)
    (hC : V ⊓ centralizer (L : Set G) = ⊥)
    {U : Subgroup G} (hUV : U ≤ V) (hU : subgroupCorank V U = 1) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) :=
  centralizer_le_of_kernel_le D S c hE hUV hU (hC ▸ bot_le)

/-- The actual lower-bound consumer, with no hyperplane or numerical premise. -/
theorem lower_bound_of_central_kernel_eq_bot
    (hmodel : FixedCodimensions D S c)
    (hE : HypothesisE61 KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V)
    (hC : V ⊓ centralizer (L : Set G) = ⊥) :
    (naturalParameter D S c : ℕ∞) ≤ globalR V :=
  lower_bound_of_hyperplanes D S hmodel hE
    (fun _U hUV hU => centralizer_le_of_central_kernel_eq_bot D S c hE hC hUV hU)

omit S c in
/-- Source uniqueness over L controls the centralizer of any nontrivial
intersection with C_V(L). This is the 4.2.13 step on printed p.767. -/
theorem escaping_hyperplane_kernel_disjoint
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ≤ N → N = normalizer (L : Set G))
    {U : Subgroup G} (hUV : U ≤ V)
    (hescape : ¬ centralizer (U : Set G) ≤ normalizer (L : Set G)) :
    U ⊓ (V ⊓ centralizer (L : Set G)) = ⊥ := by
  by_contra hn
  let W := U ⊓ (V ⊓ centralizer (L : Set G))
  have hW2 : IsPGroup 2 W := T.isPGroup'.of_injective
    (inclusion ((inf_le_left.trans hUV).trans D.le_sylow)) (inclusion_injective _)
  have hLC : L ≤ centralizer (W : Set G) :=
    le_centralizer_iff.mp (inf_le_right.trans inf_le_right)
  have hNC := Subgroup.normalizer_le_of_unique_maximalTwoLocal hunique hW2 hn
    (hLC.trans (Subgroup.centralizer_le_normalizer _))
  exact hescape ((Subgroup.centralizer_le inf_le_left).trans
    ((Subgroup.centralizer_le_normalizer _).trans hNC))

/-- After the natural hyperplane calculation and source uniqueness, any
remaining escaping hyperplane has a central kernel of order exactly two.
The nonsplit complement geometry still has to rule out this configuration. -/
theorem escaping_hyperplane_kernel_card
    (hE : HypothesisE61 KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ≤ N → N = normalizer (L : Set G))
    {U : Subgroup G} (hUV : U ≤ V) (hU : subgroupCorank V U = 1)
    (hescape : ¬ centralizer (U : Set G) ≤ normalizer (L : Set G)) :
    Nat.card ↥(V ⊓ centralizer (L : Set G)) = 2 ∧
      U ⊓ (V ⊓ centralizer (L : Set G)) = ⊥ ∧
      U ⊔ (V ⊓ centralizer (L : Set G)) = V := by
  let := D.elementary
  let C := V ⊓ centralizer (L : Set G)
  have hdis := escaping_hyperplane_kernel_disjoint D hunique hUV hescape
  have hC : C ≠ ⊥ := by
    intro hb
    exact hescape (centralizer_le_of_central_kernel_eq_bot D S c hE hb hUV hU)
  have hi : U.relIndex V = 2 := by
    rw [Subgroup.relIndex_eq_two_pow_quotient_finrank,
      ← subgroupCorank_eq_quotient_finrank,hU]
    rfl
  have hUC : U.relIndex C = Nat.card C := by
    rw [←inf_relIndex_right,hdis,relIndex_bot_left]
  have hbound := relIndex_le_of_le_right (show C ≤ V from inf_le_left)
    (show U.relIndex V ≠ 0 from index_ne_zero_of_finite)
  rw [hi,hUC] at hbound
  have hpos := C.one_lt_card_iff_ne_bot.mpr hC
  have hc : Nat.card C = 2 := by omega
  refine ⟨hc,hdis,?_⟩
  have hs : U ⊔ C ≤ V := sup_le hUV inf_le_left
  have hbig := relIndex_le_of_le_right (show C ≤ U ⊔ C from le_sup_right)
    (show U.relIndex (U ⊔ C) ≠ 0 from index_ne_zero_of_finite)
  have hsmall := relIndex_le_of_le_right hs
    (show U.relIndex V ≠ 0 from index_ne_zero_of_finite)
  rw [hUC,hc] at hbig
  rw [hi] at hsmall
  have hm := relIndex_mul_relIndex U (U ⊔ C) V le_sup_left hs
  have he : U.relIndex (U ⊔ C) = 2 := by omega
  rw [he,hi] at hm
  have hidx : (U ⊔ C).relIndex V = 1 := by omega
  exact le_antisymm hs (relIndex_eq_one.mp hidx)

/-- Source uniqueness completes every hyperplane outside the remaining
order-two central-kernel case. -/
theorem centralizer_le_of_kernel_card_ne_two
    (hE : HypothesisE61 KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ≤ N → N = normalizer (L : Set G))
    (hC : Nat.card ↥(V ⊓ centralizer (L : Set G)) ≠ 2)
    {U : Subgroup G} (hUV : U ≤ V) (hU : subgroupCorank V U = 1) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) := by
  by_contra hn
  exact hC (escaping_hyperplane_kernel_card D S c hE hunique hUV hU hn).1

/-- The parameter lower bound with the sole remaining local case separated
by the actual order of C_V(L), not a splitting assumption. -/
theorem lower_bound_of_kernel_card_ne_two
    (hmodel : FixedCodimensions D S c)
    (hE : HypothesisE61 KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ≤ N → N = normalizer (L : Set G))
    (hC : Nat.card ↥(V ⊓ centralizer (L : Set G)) ≠ 2) :
    (naturalParameter D S c : ℕ∞) ≤ globalR V :=
  lower_bound_of_hyperplanes D S hmodel hE
    (fun _U hUV hU => centralizer_le_of_kernel_card_ne_two D S c hE hunique hC hUV hU)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes
