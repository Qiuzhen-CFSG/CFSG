module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.HomocyclicCore
public import Theory.SpecificGroups.PSL3Two.Parabolics.NaturalResidual
public import Theory.GroupTheory.PCoreRestriction
public import Theory.SpecificGroups.PSL3Two.Parabolics.NaturalPointResidual

/-!
# The original point residual and the order-256 subgroup PU

The full natural action and O₂(LU)=O₂(L) first put U inside the original L.
The point-stabilizer residual moves the entire binary seed. Squaring on the
homocyclic core lifts these displacements to commutators, proving
P=[P,L₁]≤L₁. The literal intersection P∩U=VZ(U) then gives |PU|=256.
All actions use the original natural marking and the given invariant flag.

Source: Aschbacher--Smith, proof of 14.3.33(2), printed p.1004.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem closure_le_actor
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U) :
    F.U ≤ L := by
  let := h.chosen.elementary
  have he : (L ⊔ F.U).pCoreIn 2 = L.pCoreIn 2 :=
    (centerSpan_eq_join_closure_core h structural alternatives F s hne).symm.trans
      (centerSpan_eq_core h structural alternatives F s hne)
  have hULT : L ⊔ F.U ≤ L ⊔ (T : Subgroup G) :=
    sup_le_sup_left (closure_le_sylow F s) L
  intro x hx
  have hxV : x ∈ normalizer (V : Set G) :=
    (F.last ▸ F.invariant 3) (closure_le_sylow F s hx)
  obtain ⟨l, hl, heq⟩ := NormalGeometry.normalizer_action_image
    h.naturalMarking.geometryAction V le_rfl x hxV
  have hc : l⁻¹ * x ∈ centralizer (V : Set G) := by
    intro v hv
    have hh := congrArg (fun a : G => l⁻¹ * a * l) (heq v hv)
    have ht : (l⁻¹ * x) * v * (l⁻¹ * x)⁻¹ = v := by
      simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left,
        inv_mul_cancel, mul_one] using hh
    exact (mul_inv_eq_iff_eq_mul.mp ht).symm
  have hy : l⁻¹ * x ∈ L ⊔ F.U :=
    (L ⊔ F.U).mul_mem (mem_sup_left (L.inv_mem hl.1)) (mem_sup_right hx)
  have hq : l⁻¹ * x ∈ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    h.centralizer_LT_at structural ▸ ⟨hULT hy, hc⟩
  have hp := inf_pCoreIn_le_of_le 2 hULT ⟨hy, hq⟩
  rw [he] at hp
  have hh := L.mul_mem hl.1 (pCoreIn_le 2 L hp)
  simpa only [mul_inv_cancel_left] using hh

theorem core_closure_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U) :
    Nat.card (L.pCoreIn 2 ⊔ F.U : Subgroup G) = 256 := by
  have he := centerSpan_eq_core h structural alternatives F s hne
  have hp : Nat.card (L.pCoreIn 2) = 64 :=
    he ▸ (centerSpan_square_kernel_and_card h structural alternatives F s hne).2
  have hi : Nat.card (L.pCoreIn 2 ⊓ F.U : Subgroup G) = 16 :=
    he ▸ centerSpan_inf_closure_card h structural alternatives F s hne
  have hn : F.U ≤ normalizer (L.pCoreIn 2 : Set G) :=
    (closure_le_actor h structural alternatives F s hne).trans
      (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes (L.pCoreIn 2) F.U hn
  rw [hp, hi, s.core_shape.card] at hc
  omega

private noncomputable def pointProjection
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3) : L →* Matrix.PSL3Two.SL :=
  let := h.chosen.elementary
  (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.toMonoidHom.comp
    (h.naturalMarking.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))

private theorem pointProjection_surjective
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3) :
    Function.Surjective (pointProjection h) := by
  let := h.chosen.elementary
  exact (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.surjective.comp
    (h.naturalMarking.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _))

private noncomputable def seedCoordinates
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3) :
    V ≃* Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag.Model :=
  let := h.chosen.elementary
  h.naturalMarking.coordinates.toAddEquiv.toMultiplicativeRight

private theorem pointProjection_equivariant
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3) (l : L) (v : V) :
    seedCoordinates h (setupSeedAction L V h.chosen.normalizes l v) =
      Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag.slAut (pointProjection h l) (seedCoordinates h v) := by
  let := h.chosen.elementary
  apply Multiplicative.toAdd.injective
  have he := h.naturalMarking.equivariant l (Additive.ofMul v)
  have ht := (BinaryLinear.OuterCyclic.slEquivLinear 3).apply_symm_apply
    (h.naturalMarking.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l))
  have ht' := congrArg (fun a : BinaryLinear.OuterCyclic.LinearGroup 3 =>
    a (h.naturalMarking.coordinates (Additive.ofMul v))) ht
  rw [Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag.slAut_apply]
  exact he.trans ht'.symm

private theorem pointProjection_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (F : InvariantFlag T V 3) :
    ∃ z : V, z ≠ 1 ∧
      ((F.Li L 1).subgroupOf L).map (pointProjection h) =
        Matrix.PSL3Two.MarkedAutomorphisms.residual
          (MulAction.stabilizer Matrix.PSL3Two.SL (seedCoordinates h z).toAdd) := by
  let := h.chosen.elementary
  have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  obtain ⟨a, ha, hall⟩ := (Nat.card_eq_two_iff' (1 : F.Vi 1)).mp hc
  let z : V := ⟨a, F.le_seed 1 a.property⟩
  have hz : z ≠ 1 := fun he => ha (Subtype.ext (congrArg (fun x : V => (x : G)) he))
  have hmem (l : L) : pointProjection h l ∈
      MulAction.stabilizer Matrix.PSL3Two.SL (seedCoordinates h z).toAdd ↔ (l : G) ∈ F.H := by
    rw [MulAction.mem_stabilizer_iff]
    change (pointProjection h l).val.mulVec (seedCoordinates h z).toAdd = _ ↔ _
    rw [← Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag.slAut_apply]
    rw [← pointProjection_equivariant, Multiplicative.toAdd.injective.eq_iff,
      (seedCoordinates h).injective.eq_iff]
    have hn : F.H = centralizer ({(z : G)} : Set G) := by
      change normalizer (F.Vi 1 : Set G) = _
      apply le_antisymm
      · intro x hx
        exact fun y hy => by
          have he : y = (z : G) := Set.mem_singleton_iff.mp hy
          subst y
          exact normalizer_le_centralizer_of_card_two _ hc hx a a.property
      · intro x hx
        apply Subgroup.centralizer_le_normalizer
        intro y hy
        rcases eq_or_ne (⟨y, hy⟩ : F.Vi 1) 1 with he | he
        · have hy1 := congrArg Subtype.val he
          change y = 1 at hy1
          simp only [hy1, one_mul, mul_one]
        · have hey := congrArg Subtype.val (hall ⟨y, hy⟩ he)
          change y = (a : G) at hey
          rw [hey]
          exact hx z (Set.mem_singleton _)
    rw [hn, mem_centralizer_singleton_iff]
    change (⟨(l : G) * (z : G) * (l : G)⁻¹, _⟩ : V) = z ↔ (l : G) * z = z * l
    rw [Subtype.ext_iff]
    exact ⟨fun hh => mul_inv_eq_iff_eq_mul.mp hh,
      fun hh => mul_inv_eq_iff_eq_mul.mpr hh⟩
  let N := (L ⊓ F.H).subgroupOf L
  have hN : N.map (pointProjection h) =
      MulAction.stabilizer Matrix.PSL3Two.SL (seedCoordinates h z).toAdd := by
    ext x
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact (hmem l).mpr hl.2
    · intro hx
      obtain ⟨l, rfl⟩ := pointProjection_surjective h x
      exact ⟨l, ⟨l.property, (hmem l).mp hx⟩, rfl⟩
  have hLi : (pResidual 2 N).map N.subtype = (F.Li L 1).subgroupOf L := by
    apply (map_injective L.subtype_injective)
    rw [map_embedded_pResidual, map_subgroupOf_eq_of_le inf_le_left,
      map_subgroupOf_eq_of_le ((F.Li_le L 1).trans inf_le_left)]
    simp only [Li, show ¬ (3 = 5 ∧ (1 = 2 ∨ 1 = 3)) by decide, ↓reduceIte]
    rfl
  refine ⟨z, hz, ?_⟩
  rw [← hLi, map_embedded_pResidual, hN]
  rfl

private theorem seed_le_of_point_displacements
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (F : InvariantFlag T V 3) (D : Subgroup G)
    (hD : ∀ v ∈ V, ∀ l ∈ F.Li L 1, v * (l * v * l⁻¹)⁻¹ ∈ D) : V ≤ D := by
  obtain ⟨z, hz, hpoint⟩ := pointProjection_point h F
  let c := seedCoordinates h
  let E := (D.subgroupOf V).map c.toMonoidHom
  have ht : E = ⊤ := by
    apply Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag.point_residual_movement (c z)
      (fun he => hz (c.injective (he.trans c.map_one.symm)))
    intro w g hg
    obtain ⟨v, rfl⟩ := c.surjective w
    obtain ⟨l, hl, rfl⟩ := hpoint.symm ▸ hg
    refine ⟨v * (setupSeedAction L V h.chosen.normalizes l v)⁻¹, ?_, ?_⟩
    · exact hD v v.property l hl
    · simp only [map_mul, map_inv]
      exact congrArg (fun a => c v * a⁻¹) (pointProjection_equivariant h l v)
  intro v hv
  have hm : c ⟨v, hv⟩ ∈ E := ht ▸ mem_top _
  obtain ⟨w, hw, he⟩ := hm
  have hh : (w : G) = v := congrArg Subtype.val (c.injective he)
  exact hh ▸ hw

/-- The original point residual moves all of P: squaring transports its
natural seed displacements to genuine commutators in the homocyclic core. -/
theorem core_eq_point_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U) :
    L.pCoreIn 2 = ⁅L.pCoreIn 2, F.Li L 1⁆ := by
  let := centerSpan_abelian h structural F s
  let P := centerSpan L F
  let C := ⁅P, F.Li L 1⁆
  have hn : F.Li L 1 ≤ normalizer (P : Set G) :=
    ((F.Li_le L 1).trans inf_le_left).trans (le_normalizer_conjugateSpanBy _ _)
  have hCP : C ≤ P := le_normalizer_iff_commutator_le_left.mp hn
  obtain ⟨f, hf, hfx⟩ := centerSpan_square_map h structural F s
  let D := ((C.subgroupOf P).map f).map V.subtype
  have hVD : V ≤ D := by
    apply seed_le_of_point_displacements h F D
    intro v hv l hl
    obtain ⟨y, hy, hy2⟩ := seed_exists_centerSpan_square h F s hv
    have ht : l * y * l⁻¹ ∈ P := (mem_normalizer_iff.mp (hn hl) y).mp hy
    have hc : Commute y (l * y * l⁻¹)⁻¹ := by
      exact congrArg Subtype.val (mul_comm (⟨y, hy⟩ : P) ⟨_, P.inv_mem ht⟩)
    have hm : ⁅y, l⁆ ∈ C := commutator_mem_commutator hy hl
    refine ⟨f ⟨⁅y, l⁆, hCP hm⟩, ⟨⟨⁅y, l⁆, hCP hm⟩, hm, rfl⟩, ?_⟩
    change (f ⟨⁅y, l⁆, hCP hm⟩ : G) = _
    rw [hfx]
    have he : ⁅y, l⁆ = y * (l * y * l⁻¹)⁻¹ := by simp [commutatorElement_def, mul_assoc]
    change ⁅y, l⁆ ^ 2 = _
    rw [he, hc.mul_pow, inv_pow, ← MulAut.conj_apply, ← map_pow, hy2, MulAut.conj_apply]
  have hex (v : G) (hv : v ∈ V) : ∃ c ∈ C, c ^ 2 = v := by
    obtain ⟨a, ⟨b, hb, rfl⟩, he⟩ := hVD hv
    exact ⟨b, hb, (hfx b).symm.trans he⟩
  have hVC : V ≤ C := by
    intro v hv
    obtain ⟨c, hc, rfl⟩ := hex v hv
    exact C.pow_mem hc 2
  have heP : P = C := by
    apply le_antisymm ?_ hCP
    intro x hx
    obtain ⟨c, hc, he⟩ := hex (x ^ 2) (centerSpan_square_mem_seed h structural F s hx)
    have hxc : Commute x c⁻¹ := by
      exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : P) ⟨_, P.inv_mem (hCP hc)⟩)
    have hs : (x * c⁻¹) ^ 2 = 1 := by rw [hxc.mul_pow, inv_pow, he, mul_inv_cancel]
    have hv := (centerSpan_square_kernel_and_card h structural alternatives F s hne).1
      _ (P.mul_mem hx (P.inv_mem (hCP hc))) |>.mp hs
    have hh := C.mul_mem (hVC hv) hc
    simpa only [inv_mul_cancel_right] using hh
  simpa only [P, C, centerSpan_eq_core h structural alternatives F s hne] using heP

/-- O₂(L) lies in the original point residual L₁. -/
theorem core_le_point_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U) :
    L.pCoreIn 2 ≤ F.Li L 1 := by
  rw [core_eq_point_commutator h structural alternatives F s hne]
  apply le_normalizer_iff_commutator_le_right.mp
  have hPH : L.pCoreIn 2 ≤ F.H :=
    (h.centralizer_L.symm.le.trans inf_le_right).trans
      ((centralizer_le (F.le_seed 1)).trans (Subgroup.centralizer_le_normalizer _))
  change L.pCoreIn 2 ≤ normalizer
    (((pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype) : Set G)
  exact (le_inf (pCoreIn_le 2 L) hPH).trans
    ((L ⊓ F.H).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pResidual 2 (L ⊓ F.H : Subgroup G))))

/-- The order-256 source subgroup PU is an actual subgroup of L∩H. -/
theorem core_closure_le_point_normalizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U) :
    L.pCoreIn 2 ⊔ F.U ≤ L ⊓ F.H := by
  let := h.chosen.elementary
  exact sup_le ((core_le_point_residual h structural alternatives F s hne).trans (F.Li_le L 1))
    (le_inf (closure_le_actor h structural alternatives F s hne) F.U_le_H)

/-- The original point residual has order 64·12=768. -/
theorem point_residual_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U) :
    Nat.card (F.Li L 1) = 768 := by
  let := h.chosen.elementary
  let A := (F.Li L 1).subgroupOf L
  let f := pointProjection h
  have hk : f.ker = pCore 2 L := by
    change ((BinaryLinear.OuterCyclic.slEquivLinear 3).symm.toMonoidHom.comp
      (h.naturalMarking.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))).ker = _
    rw [MonoidHom.ker_comp_of_injective _ _ (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.injective,
      MonoidHom.ker_comp_of_injective _ _ h.naturalMarking.quotientEquiv.injective,
      QuotientGroup.ker_mk']
  have hPA : pCore 2 L ≤ A := by
    intro x hx
    exact core_le_point_residual h structural alternatives F s hne
      (mem_map_of_mem L.subtype hx)
  let q := f.comp A.subtype
  have hker : Nat.card q.ker = 64 := by
    have he : q.ker = (pCore 2 L).subgroupOf A := by
      change f.ker.comap A.subtype = _
      rw [hk]
      rfl
    rw [he, Nat.card_congr (subgroupOfEquivOfLe hPA).toEquiv]
    rw [← card_map_of_injective L.subtype_injective]
    change Nat.card (L.pCoreIn 2) = 64
    rw [← centerSpan_eq_core h structural alternatives F s hne]
    exact (centerSpan_square_kernel_and_card h structural alternatives F s hne).2
  have hrange : Nat.card q.range = 12 := by
    have he : q.range = A.map f := by
      rw [MonoidHom.range_comp, range_subtype]
    rw [he]
    obtain ⟨z, hz, hp⟩ := pointProjection_point h F
    rw [hp]
    apply BinaryLinearThree.naturalPoint_residual_card
    exact fun he => hz ((seedCoordinates h).injective
      ((Multiplicative.toAdd.injective he).trans (seedCoordinates h).map_one.symm))
  have hc := q.ker.card_mul_index
  rw [index_ker, hker, hrange] at hc
  have he := Nat.card_congr
    (subgroupOfEquivOfLe ((F.Li_le L 1).trans inf_le_left)).toEquiv
  change Nat.card A = Nat.card (F.Li L 1) at he
  omega

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
