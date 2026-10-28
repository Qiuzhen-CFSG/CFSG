module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableQuinticSource.PartnerTwoFour

/-!
# The two actual support lines of the second four-group

Project the central partner involution onto the two original Thompson
planes. Sylow support preservation or exchange fixes or swaps its two
components, so their span is Sylow-central modulo Uc. It is therefore
contained in E₂, and the proved order-four bound makes it exactly E₂.
The partner line is the diagonal product of the two nontrivial components.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The second four-group splits into one line in each original marked
plane; the central partner line is their diagonal product. -/
theorem PreparedChosenModule.decomposable_five_partner_two_second_seed_lines
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc) = 2 →
      (let Z := thompsonPlane T V (c.ambientFactor d s.first).space
       let C := M ⊓ centralizer (Z : Set G)
       letI := caseI_module_centralizer_normal (Z1 := Z) h.normalized
       Nat.card (pResidual 2 (C ⧸
         (M ⊓ centralizer (V : Set G)).subgroupOf C)) = 5) →
      let E₂ := thompsonFixed T V ⊓
        commutatorPreimage (T : Subgroup G) (T : Subgroup G) (localModule T Mc)
      let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
      let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
      ∃ a ∈ Z₁, ∃ b ∈ Z₂, a ≠ 1 ∧ b ≠ 1 ∧
        localModule T Mc = zpowers (a*b) ∧ E₂ = zpowers a ⊔ zpowers b ∧
        (T : Subgroup G) ⊓ centralizer ({a} : Set G) =
          (T : Subgroup G) ⊓ normalizer (plane V (c.ambientFactor d s.first).space : Set G) ∧
        (T : Subgroup G) ⊓ centralizer (E₂ : Set G) =
          (T : Subgroup G) ⊓ normalizer (plane V (c.ambientFactor d s.first).space : Set G) ∧
        (((T : Subgroup G) ⊓ centralizer ({a} : Set G)).subgroupOf (T : Subgroup G)).Normal := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hratio hfive hcU hcard E₂ Z₁ Z₂
  let E := thompsonFixed T V
  let Uc := localModule T Mc
  have hfour : Nat.card E₂ = 4 := h.decomposable_five_partner_two_second_seed_card_four
    hG T hempty hM hmany hJ hu hne hfull c d hd s π hp hs hdec hratio hfive hcU hcard
  have hUE : Uc ≤ E := (h.decomposable_five_partner_control
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hratio hfive).2.2
  have hUZ := (h.decomposable_five_partner_two_fixed_line
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hratio hfive hcU).1
  have hUT : Uc ≤ centralizer (T : Set G) := by
    rw [show Uc = centralInvolutions T from hUZ]
    exact centralInvolutions_le_centralizer_sylow T
  have hTU : (T : Subgroup G) ≤ normalizer (Uc : Set G) :=
    (le_centralizer_iff.mp hUT).trans (Subgroup.centralizer_le_normalizer _)
  have hET : E ≤ (T : Subgroup G) := fun e he => ChapterB.thompsonJ_le _ _
    (((mem_omegaOneCenterAmbient_iff _ e).mp (h.thompsonFixed_le_omega T hM he)).1)
  have hZ₁E : Z₁ ≤ E := inf_le_right
  have hZ₂E : Z₂ ≤ E := inf_le_right
  have hZ₁V : Z₁ ≤ V := hZ₁E.trans inf_le_left
  have hZ₂V : Z₂ ≤ V := hZ₂E.trans inf_le_left
  have hnorm : Z₂ ≤ normalizer (Z₁ : Set G) :=
    (hZ₂V.trans (V.le_centralizer.trans (centralizer_le hZ₁V))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hdis : Disjoint Z₁ Z₂ := disjoint_iff.mpr s.thompson_disjoint
  obtain ⟨t, ht, hout⟩ : ∃ t ∈ (T : Subgroup G),
      t ∉ normalizer (plane V (c.ambientFactor d s.first).space : Set G) := by
    by_contra! hall
    have hh := relIndex_eq_one.mpr (le_inf le_rfl hall)
    rw [s.stabilizer_index] at hh
    contradiction
  have hex := s.thompson_exchanges t ht hout
  change Z₁.map (MulAut.conj t).toMonoidHom = Z₂ ∧
    Z₂.map (MulAut.conj t).toMonoidHom = Z₁ at hex
  have hUcNe : Uc ≠ ⊥ := (one_lt_card_iff_ne_bot Uc).mp (by rw [hcU]; decide)
  obtain ⟨u, huNe⟩ := ne_bot_iff_exists_ne_one.mp hUcNe
  have huG : (u : G) ≠ 1 := fun he => huNe (Subtype.ext he)
  have hprod : (u : G) ∈ (Z₁ : Set G) * (Z₂ : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left Z₁ Z₂ hnorm]
    exact s.thompson_split ▸ hUE u.property
  obtain ⟨a, ha, b, hb, hab⟩ := hprod
  change a*b = (u : G) at hab
  have habComm : a*b = b*a := setLike_mul_comm (hZ₁V ha) (hZ₂V hb)
  have hfix (x : G) (hx : x ∈ (T : Subgroup G)) : (MulAut.conj x) (u : G) = u :=
    mul_inv_eq_iff_eq_mul.mpr (hUT u.property x hx)
  have hane : a ≠ 1 := by
    intro he
    have huB : (u : G) ∈ Z₂ := hab ▸ (by simpa [he] using hb)
    have huA : (u : G) ∈ Z₁ := hfix t ht ▸
      (hex.2 ▸ mem_map_of_mem (MulAut.conj t).toMonoidHom huB)
    exact huG (disjoint_def.mp hdis huA huB)
  have hbne : b ≠ 1 := by
    intro he
    have huA : (u : G) ∈ Z₁ := hab ▸ (by simpa [he] using ha)
    have huB : (u : G) ∈ Z₂ := hfix t ht ▸
      (hex.1 ▸ mem_map_of_mem (MulAut.conj t).toMonoidHom huA)
    exact huG (disjoint_def.mp hdis huA huB)
  have hperm (x : G) (hx : x ∈ (T : Subgroup G)) :
      ((MulAut.conj x) a = a ∧ (MulAut.conj x) b = b) ∨
        ((MulAut.conj x) a = b ∧ (MulAut.conj x) b = a) := by
    let α := MulAut.conj x
    have hmul : α a * α b = a*b := by
      rw [← map_mul, hab, hfix x hx]
    by_cases hxN : x ∈ normalizer (plane V (c.ambientFactor d s.first).space : Set G)
    · have hn := s.thompson_normalized ⟨hx, hxN⟩
      have hαa : α a ∈ Z₁ := (mem_normalizer_iff.mp hn.1 a).mp ha
      have hαb : α b ∈ Z₂ := (mem_normalizer_iff.mp hn.2 b).mp hb
      have he := mul_injective_of_disjoint hdis
        (a₁ := (⟨α a, hαa⟩, ⟨α b, hαb⟩)) (a₂ := (⟨a, ha⟩, ⟨b, hb⟩)) hmul
      exact Or.inl ⟨congrArg (fun p : Z₁ × Z₂ => (p.1 : G)) he,
        congrArg (fun p : Z₁ × Z₂ => (p.2 : G)) he⟩
    · have hxswap := s.thompson_exchanges x hx hxN
      change Z₁.map α.toMonoidHom = Z₂ ∧ Z₂.map α.toMonoidHom = Z₁ at hxswap
      have hαa : α a ∈ Z₂ := hxswap.1 ▸ mem_map_of_mem α.toMonoidHom ha
      have hαb : α b ∈ Z₁ := hxswap.2 ▸ mem_map_of_mem α.toMonoidHom hb
      have hmul' : α b * α a = a*b := by
        rw [← map_mul, ← habComm, map_mul]
        exact hmul
      have he := mul_injective_of_disjoint hdis
        (a₁ := (⟨α b, hαb⟩, ⟨α a, hαa⟩)) (a₂ := (⟨a, ha⟩, ⟨b, hb⟩)) hmul'
      exact Or.inr ⟨congrArg (fun p : Z₁ × Z₂ => (p.2 : G)) he,
        congrArg (fun p : Z₁ × Z₂ => (p.1 : G)) he⟩
  have ha2 : a^2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) a (hZ₁V ha)
  have hb2 : b^2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) b (hZ₂V hb)
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ha2)
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hb2)
  have habU : a*b ∈ Uc := hab.symm ▸ u.property
  have haK : a ∈ commutatorPreimage (T : Subgroup G) (T : Subgroup G) Uc := by
    apply (mem_commutatorPreimage_iff _ _ _ hTU a).mpr
    refine ⟨hET (hZ₁E ha), ?_⟩
    intro x hx
    have he : ⁅a,x⁆ = a*((MulAut.conj x) a) := by
      simp only [commutatorElement_def, hai, MulAut.conj_apply, mul_assoc]
    rw [he]
    rcases hperm x hx with hf | hs
    · rw [hf.1, ← pow_two, ha2]
      exact Uc.one_mem
    · rw [hs.1]
      exact habU
  have hbK : b ∈ commutatorPreimage (T : Subgroup G) (T : Subgroup G) Uc := by
    apply (mem_commutatorPreimage_iff _ _ _ hTU b).mpr
    refine ⟨hET (hZ₂E hb), ?_⟩
    intro x hx
    have he : ⁅b,x⁆ = b*((MulAut.conj x) b) := by
      simp only [commutatorElement_def, hbi, MulAut.conj_apply, mul_assoc]
    rw [he]
    rcases hperm x hx with hf | hs
    · rw [hf.2, ← pow_two, hb2]
      exact Uc.one_mem
    · rw [hs.2, ← habComm]
      exact habU
  have hA : zpowers a ≤ Z₁ := zpowers_le.mpr ha
  have hB : zpowers b ≤ Z₂ := zpowers_le.mpr hb
  have hAc : Nat.card (zpowers a) = 2 := by rw [Nat.card_zpowers, orderOf_eq_prime ha2 hane]
  have hBc : Nat.card (zpowers b) = 2 := by rw [Nat.card_zpowers, orderOf_eq_prime hb2 hbne]
  have hJcard : Nat.card (zpowers a ⊔ zpowers b : Subgroup G) = 4 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
      ((hB.trans (hZ₂V.trans (V.le_centralizer.trans (centralizer_le (hA.trans hZ₁V))))).trans
        (Subgroup.centralizer_le_normalizer _)) (hdis.mono hA hB), hAc, hBc]
  have hJE₂ : zpowers a ⊔ zpowers b ≤ E₂ := sup_le
    (zpowers_le.mpr ⟨hZ₁E ha, haK⟩) (zpowers_le.mpr ⟨hZ₂E hb, hbK⟩)
  have hE₂J : E₂ = zpowers a ⊔ zpowers b :=
    (eq_of_le_of_card_ge hJE₂ (by rw [hfour, hJcard])).symm
  have hU : Uc = zpowers (a*b) := (eq_of_le_of_card_ge (zpowers_le.mpr habU) (by
    have hh := (one_lt_card_iff_ne_bot (zpowers (a*b))).mpr
      (by intro he; exact huG (hab ▸ (show a*b=1 from mem_bot.mp (he ▸ mem_zpowers (a*b)))))
    change Nat.card Uc = 2 at hcU
    omega)).symm
  let S₀ := (T : Subgroup G) ⊓ normalizer (plane V (c.ambientFactor d s.first).space : Set G)
  have hSfix (x : G) (hx : x ∈ S₀) :
      (MulAut.conj x) a = a ∧ (MulAut.conj x) b = b := by
    rcases hperm x hx.1 with hf | hs
    · exact hf
    · have hn := (s.thompson_normalized hx).1
      have hbA : b ∈ Z₁ := hs.1 ▸ ((mem_normalizer_iff.mp hn a).mp ha)
      exact (hbne (disjoint_def.mp hdis hbA hb)).elim
  have hSa : S₀ ≤ centralizer ({a} : Set G) := by
    intro x hx z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact (mul_inv_eq_iff_eq_mul.mp (hSfix x hx).1).symm
  have hpoint : (T : Subgroup G) ⊓ centralizer ({a} : Set G) = S₀ := by
    apply le_antisymm
    · intro x hx
      refine ⟨hx.1, ?_⟩
      by_contra hn
      have hxswap := (s.thompson_exchanges x hx.1 hn).1
      change Z₁.map (MulAut.conj x).toMonoidHom = Z₂ at hxswap
      have hxa : (MulAut.conj x) a = a := by
        change x*a*x⁻¹ = a
        rw [← hx.2 a (Set.mem_singleton a), mul_inv_cancel_right]
      have haB : a ∈ Z₂ := hxa ▸ (hxswap ▸ mem_map_of_mem (MulAut.conj x).toMonoidHom ha)
      exact hane (disjoint_def.mp hdis ha haB)
    · exact le_inf inf_le_left hSa
  have hSE₂ : S₀ ≤ centralizer (E₂ : Set G) := by
    apply le_centralizer_iff.mpr
    apply hE₂J.le.trans
    apply sup_le <;> apply zpowers_le.mpr
    · intro x hx
      exact mul_inv_eq_iff_eq_mul.mp (hSfix x hx).1
    · intro x hx
      exact mul_inv_eq_iff_eq_mul.mp (hSfix x hx).2
  have hwhole : (T : Subgroup G) ⊓ centralizer (E₂ : Set G) = S₀ := by
    apply le_antisymm
    · exact ((inf_le_inf_left _ (centralizer_le
        (show ({a} : Set G) ⊆ E₂ from Set.singleton_subset_iff.mpr ⟨hZ₁E ha, haK⟩)))).trans hpoint.le
    · exact le_inf inf_le_left hSE₂
  refine ⟨a, ha, b, hb, hane, hbne, hU, hE₂J, hpoint, hwhole, ?_⟩
  rw [hpoint]
  exact s.stabilizer_normal

end CFSG.Quasithin.Chapter15.Section01
