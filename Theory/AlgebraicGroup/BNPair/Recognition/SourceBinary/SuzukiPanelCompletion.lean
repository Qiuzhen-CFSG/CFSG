module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiCartanKernels
public import Theory.SpecificGroups.Suzuki.SmallAutomorphisms

/-!
# Completing the Suzuki root marking to the faithful endpoint

Let K be the core of the entire Borel in its marked endpoint P, and R the
canonical root-generated subgroup. The root projection R → P/K has central
kernel. Once the source Cartan lies in R K, the split factorization and a
root reflection give P = R K. Thus a centerless R identifies the entire
faithful endpoint quotient, preserving the literal projection.

For a positive Suzuki parameter the proved full Cartan factorization gives
H ≤ R K. At parameter zero, the root has order four and a nontrivial square,
so it is cyclic; its automorphism group has order two. The odd Cartan acts
trivially and lies in K. Both cases therefore give the full Suzuki quotient.
A single Sylow conjugation pins the supplied root marking to the standard
matrix root. The full Borel then maps to that root's normalizer.

Source: Fong--Seitz I (3B), (5C), (6C), (6H), pp.13,25--26,40--41,51;
DGS, Groups and Graphs (1985), Theorem D, p.224. This fills the full-panel
marking used by the Ree source charts; no Weyl order, original-factor
perfectness or marking of the whole endpoint quotient is assumed here.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.PanelCompletion
open ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)

def rootPanelMap : rankOne Q split i →* (Endpoint Q i ⧸ panelKernel Q i) :=
  (QuotientGroup.mk' _).comp (inclusion (rankOne_le_parabolic Q split i))

@[simp] theorem rootPanelMap_apply (r : rankOne Q split i) :
    rootPanelMap Q split i r = QuotientGroup.mk' (panelKernel Q i)
      (inclusion (rankOne_le_parabolic Q split i) r) := by rfl

theorem rootPanelMap_ker : (rootPanelMap Q split i).ker =
    (localKernel Q i).subgroupOf (rankOne Q split i) := by
  ext r
  change QuotientGroup.mk' _ (inclusion (rankOne_le_parabolic Q split i) r) = 1 ↔ _
  change ((inclusion (rankOne_le_parabolic Q split i) r : Endpoint Q i) :
    Endpoint Q i ⧸ panelKernel Q i) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  constructor
  · intro hr
    exact mem_map_of_mem (Endpoint Q i).subtype hr
  · rintro ⟨s,hs,he⟩
    have he' : s = inclusion (rankOne_le_parabolic Q split i) r := Subtype.ext he
    exact he' ▸ hs

theorem rootPanelMap_injective (hz : center (rankOne Q split i) = ⊥) :
    Function.Injective (rootPanelMap Q split i) := by
  apply (rootPanelMap Q split i).ker_eq_bot_iff.mp
  rw [rootPanelMap_ker, ← RootLocalCover.projection_ker]
  exact eq_bot_iff.mpr (hz ▸ RootLocalCover.projection_ker_central Q split i)

theorem endpoint_eq_root_sup_kernel
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (hH : Q.tits.B ⊓ Q.tits.N ≤ rankOne Q split i ⊔ localKernel Q i) :
    Endpoint Q i = rankOne Q split i ⊔ localKernel Q i := by
  apply le_antisymm
  · let s := UnitarySource.actorReflection Q split i
    rw [Endpoint, UnitarySource.endpoint_eq_borel_sup_lift Q i s.val s.class_eq]
    apply sup_le
    · rw [← split.factorization]
      exact sup_le (le_sup_left.trans (localClosure_le_rankOne_sup_kernel Q split i hV)) hH
    · exact (closure_le _).mpr (Set.singleton_subset_iff.mpr (mem_sup_left s.mem_rankOne))
  · exact sup_le (rankOne_le_parabolic Q split i)
      ((localKernel_le_borel Q i).trans (Q.tits.B_le_standardParabolic _))

theorem rootPanelMap_surjective
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (hH : Q.tits.B ⊓ Q.tits.N ≤ rankOne Q split i ⊔ localKernel Q i) :
    Function.Surjective (rootPanelMap Q split i) := by
  intro z
  induction z using QuotientGroup.induction_on with
  | H z =>
    have hz : (z : X ⧸ Q.D) ∈ rankOne Q split i ⊔ localKernel Q i :=
      (endpoint_eq_root_sup_kernel Q split i hV hH).le z.property
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _
        ((rankOne_le_parabolic Q split i).trans (localKernel_parabolic_normalizes Q i))] at hz
    obtain ⟨r,hr,k,hk,he⟩ := hz
    refine ⟨⟨r,hr⟩,QuotientGroup.eq.mpr ?_⟩
    have hk' : r⁻¹*(z : X ⧸ Q.D) ∈ localKernel Q i := by
      rw [←he,inv_mul_cancel_left]
      exact hk
    have hk'' : (inclusion (rankOne_le_parabolic Q split i) ⟨r,hr⟩)⁻¹*z ∈
        (localKernel Q i).subgroupOf (Endpoint Q i) := hk'
    simpa only [localKernel_subgroupOf, panelKernel, endpointBorel] using hk''

def rootPanelEquiv (hz : center (rankOne Q split i) = ⊥)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (hH : Q.tits.B ⊓ Q.tits.N ≤ rankOne Q split i ⊔ localKernel Q i) :
    rankOne Q split i ≃* (Endpoint Q i ⧸ panelKernel Q i) :=
  MulEquiv.ofBijective (rootPanelMap Q split i)
    ⟨rootPanelMap_injective Q split i hz, rootPanelMap_surjective Q split i hV hH⟩

theorem rootPanelMap_borel : (quotientBorel Q i).comap (rootPanelMap Q split i) =
    Q.tits.B.subgroupOf (rankOne Q split i) := by
  change ((quotientBorel Q i).comap (QuotientGroup.mk' (panelKernel Q i))).comap
    (inclusion (rankOne_le_parabolic Q split i)) = _
  rw [quotientBorel_comap]
  rfl

theorem small_suzuki_cartan_le_kernel
    (ν : simpleRoot Q split i ≃* SuzukiRootSubgroup 0) :
    Q.tits.B ⊓ Q.tits.N ≤ localKernel Q i := by
  have hc : Nat.card (simpleRoot Q split i) = 4 := by
    rw [Nat.card_congr ν.toEquiv, matrixRoot_card]
    norm_num
  obtain ⟨a,ha⟩ := suzuki_root_exists_nontrivial_square 0
  have hne : (ν.symm a)^2 ≠ 1 := by
    intro he
    apply ha
    have he' := congrArg ν he
    simpa only [map_pow,ν.apply_symm_apply,map_one] using he'
  have hd : orderOf (ν.symm a) ∣ 4 := by
    simpa only [hc] using orderOf_dvd_natCard (ν.symm a)
  have hn : ¬ orderOf (ν.symm a) ∣ 2 := fun h => hne (orderOf_dvd_iff_pow_eq_one.mp h)
  have ho : orderOf (ν.symm a) = 4 := by
    have hb := Nat.le_of_dvd (by decide : 0 < 4) hd
    interval_cases horder : orderOf (ν.symm a) <;> norm_num at *
  let : IsCyclic (simpleRoot Q split i) := isCyclic_of_orderOf_eq_card _ (ho.trans hc.symm)
  have haut : Nat.card (MulAut (simpleRoot Q split i)) = 2 := by
    rw [IsCyclic.card_mulAut,hc]
    decide
  intro h hh
  let h' : ↥(Q.tits.B ⊓ Q.tits.N) := ⟨h,hh⟩
  let f := simpleRootAction Q split i
  have hd₂ : orderOf (f h') ∣ 2 := haut ▸ orderOf_dvd_natCard _
  have hdH : orderOf (f h') ∣ Nat.card (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) :=
    (orderOf_map_dvd f h').trans (orderOf_dvd_natCard h')
  have hf : f h' = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes split.odd hd₂ hdH)
  have hk : h' ∈ (cartanPanelMap Q i).ker := by
    rw [←simpleRootAction_kernel Q split i]
    exact hf
  rw [cartanPanelMap_kernel] at hk
  exact hk

theorem suzuki_cartan_le_root_sup_kernel
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    {m : ℕ} (μ : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (ν : simpleRoot Q split i ≃* SuzukiRootSubgroup m) :
    Q.tits.B ⊓ Q.tits.N ≤ rankOne Q split i ⊔ localKernel Q i := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact (small_suzuki_cartan_le_kernel Q split i ν).trans le_sup_right
  · intro h hh
    obtain ⟨c,k,he⟩ := suzuki_cartan_factorization Q split i hV hm μ ν ⟨h,hh⟩
    have hk : (k.val : X ⧸ Q.D) ∈ localKernel Q i :=
      (SetLike.ext_iff.mp (cartanPanelMap_kernel Q i) k.val).mp k.property
    have hval := congrArg Subtype.val he
    change h = (c.val : X ⧸ Q.D)*(k.val : X ⧸ Q.D) at hval
    rw [hval]
    exact mul_mem_sup c.property hk

private theorem suzuki_center (m : ℕ) : center (SuzukiMatrixGroup m) = ⊥ := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact suzukiZero_center_eq_bot
  · let : IsSimpleGroup (SuzukiMatrixGroup m) :=
      (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
    rcases (inferInstance : (center (SuzukiMatrixGroup m)).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m hm
        (Group.isSolvable_of_comm (fun x y =>
          (mem_center_iff.mp (h ▸ mem_top x) y).symm))).elim

/-- Adjust the given root-group marking by one inner automorphism, so its
whole canonical root is the fixed matrix root. -/
theorem suzuki_root_pinning {m : ℕ}
    (μ : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (ν : simpleRoot Q split i ≃* SuzukiRootSubgroup m) :
    ∃ g : SuzukiMatrixGroup m,
      ((simpleRoot Q split i).subgroupOf (rankOne Q split i)).map
        (μ.trans (MulAut.conj g)).toMonoidHom = SuzukiRootSubgroup m := by
  obtain ⟨S,hS⟩ := simpleRoot_sylow_of_suzuki Q split i μ ν
  let T := S.mapSurjective (f := μ.toMonoidHom) μ.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (↥(SuzukiMatrixGroup m)) T (matrixRootSylow m)
  refine ⟨g,?_⟩
  change ((simpleRoot Q split i).subgroupOf (rankOne Q split i)).map
    ((MulAut.conj g).toMonoidHom.comp μ.toMonoidHom) = _
  rw [← map_map, ← hS]
  change (T : Subgroup (SuzukiMatrixGroup m)).map (MulAut.conj g).toMonoidHom = _
  change ((g • T : Sylow 2 (SuzukiMatrixGroup m)) : Subgroup (SuzukiMatrixGroup m)) = _
  rw [hg, matrixRootSylow_carrier]

/-- The full faithful endpoint quotient is Suzuki, with its entire Borel and
root marked in the standard matrix coordinates, including parameter zero. -/
theorem exists_suzuki_panel_marking
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    {m : ℕ} (μ : rankOne Q split i ≃* SuzukiMatrixGroup m)
    (ν : simpleRoot Q split i ≃* SuzukiRootSubgroup m) :
    ∃ (g : SuzukiMatrixGroup m)
      (σ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m),
      (∀ r, σ (rootPanelMap Q split i r) = g * μ r * g⁻¹) ∧
      (rootProjection Q split i).range.map σ.toMonoidHom = SuzukiRootSubgroup m ∧
      (quotientBorel Q i).map σ.toMonoidHom =
        normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)) := by
  have hz : center (rankOne Q split i) = ⊥ := by
    apply eq_bot_iff.mpr
    intro r hr
    have hμ := MulEquivClass.apply_mem_center μ hr
    change μ r ∈ center (SuzukiMatrixGroup m) at hμ
    rw [suzuki_center,mem_bot] at hμ
    exact μ.injective (hμ.trans μ.map_one.symm)
  let e := rootPanelEquiv Q split i hz hV (suzuki_cartan_le_root_sup_kernel Q split i hV μ ν)
  obtain ⟨g,hg⟩ := suzuki_root_pinning Q split i μ ν
  let η := μ.trans (MulAut.conj g)
  let σ := e.symm.trans η
  have he (r : rankOne Q split i) : σ (rootPanelMap Q split i r) = η r :=
    congrArg η (e.symm_apply_apply r)
  have hf : σ.toMonoidHom.comp (rootPanelMap Q split i) = η.toMonoidHom := by
    ext r : 1
    exact he r
  refine ⟨g,σ,fun r => he r,?_,?_⟩
  · have hp : rootProjection Q split i = (rootPanelMap Q split i).comp
        (inclusion (show simpleRoot Q split i ≤ rankOne Q split i from le_sup_left)) := rfl
    rw [hp,MonoidHom.range_comp,map_map,hf,inclusion_range]
    exact hg
  · have hb : Q.tits.B.subgroupOf (rankOne Q split i) =
        normalizer (((simpleRoot Q split i).subgroupOf (rankOne Q split i)) : Set _) := by
      ext r
      exact rankOne_borel_iff_root_normalizer Q split i hV r
    have hmap : (Q.tits.B.subgroupOf (rankOne Q split i)).map e.toMonoidHom = quotientBorel Q i := by
      change ((Q.tits.B.subgroupOf (rankOne Q split i)).map (rootPanelMap Q split i)) = _
      rw [← rootPanelMap_borel, map_comap_eq_self_of_surjective (rootPanelMap_surjective Q split i hV
        (suzuki_cartan_le_root_sup_kernel Q split i hV μ ν))]
    rw [←hmap,map_map]
    change (Q.tits.B.subgroupOf (rankOne Q split i)).map
      (σ.toMonoidHom.comp (rootPanelMap Q split i)) = _
    rw [hf,hb,map_normalizer_eq_of_bijective _ η.bijective]
    rw [hg]

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.PanelCompletion
