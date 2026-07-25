/-
Authors: OpenAI, Yusen Tang
-/

module

public import FeitThompson.BGsection6.lemma_6_3_b_2
import FeitThompson.SubgroupConj

open scoped MatrixGroups Pointwise TensorProduct

/-! # Theorem 6.4 from BG Section 6 -/

public theorem conjBy_eq_of_mem_normalizer_local
    {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (G := G) H) :
    H.conjBy g = H := by
  ext x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    simpa [Subgroup.conjBy, MulAut.conj_apply, mul_assoc] using
      ((Subgroup.mem_normalizer_iff).1 hg y).1 hy
  · intro hx
    refine Subgroup.mem_map.mpr ?_
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · have hgInv : g⁻¹ ∈ Subgroup.normalizer (G := G) H :=
        (Subgroup.normalizer (G := G) (H : Set G)).inv_mem hg
      simpa [mul_assoc] using ((Subgroup.mem_normalizer_iff).1 hgInv x).1 hx
    · simp [MulAut.conj_apply, mul_assoc]

public theorem mem_normalizer_of_conjBy_eq_local
    {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hg : H.conjBy g = H) :
    g ∈ Subgroup.normalizer (G := G) H := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hx' : g * x * g⁻¹ ∈ H.conjBy g := by
      refine Subgroup.mem_map.mpr ?_
      exact ⟨x, hx, by simp [MulAut.conj_apply, mul_assoc]⟩
    simpa [hg] using hx'
  · intro hx
    have hx' : g * x * g⁻¹ ∈ H.conjBy g := by simpa [hg] using hx
    rcases Subgroup.mem_map.mp hx' with ⟨y, hy, hyx⟩
    have : x = y := by
      calc
        x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g⁻¹ * (MulAut.conj g y) * g := by rw [← hyx]; rfl
        _ = y := by simp [MulAut.conj_apply, mul_assoc]
    simpa [this] using hy

private theorem map_mk'_map_conj_eq_local64
    {G : Type*} [Group G] {N H : Subgroup G} [N.Normal] (g : G) :
    (H.map (MulAut.conj g).toMonoidHom).map (QuotientGroup.mk' N) =
      (H.map (QuotientGroup.mk' N)).map (MulAut.conj ((QuotientGroup.mk' N) g)).toMonoidHom := by
  ext q
  constructor
  · rintro ⟨_, hx, rfl⟩
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨(QuotientGroup.mk' N) y, ⟨y, hy, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨_, hx, rfl⟩
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨g * y * g⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨y, hy, by simp [MulAut.conj_apply, mul_assoc]⟩
    · simp [MulAut.conj_apply, mul_assoc]

private theorem natCard_lt_of_proper_subgroup_local64
    {G : Type*} [Group G] [Finite G] {K : Subgroup G} (hK : K < (⊤ : Subgroup G)) :
    Nat.card K < Nat.card G := by
  have hle : Nat.card K ≤ Nat.card G := Subgroup.card_le_card_group (H := K)
  have hne : Nat.card K ≠ Nat.card G := by
    intro hcard
    exact hK.ne ((Subgroup.card_eq_iff_eq_top (H := K)).1 hcard)
  exact lt_of_le_of_ne hle hne

private theorem measure_lt_of_proper_subgroup_local64
    {G : Type*} [Group G] [Finite G] {H K : Subgroup G} (hK : K < (⊤ : Subgroup G)) :
    Nat.card K + Nat.card H < Nat.card G + Nat.card H := by
  exact Nat.add_lt_add_right (natCard_lt_of_proper_subgroup_local64 hK) _

private theorem measure_lt_of_quotient_local64
    {G : Type*} [Group G] [Finite G] {N H : Subgroup G} [N.Normal]
    (hN : N ≠ (⊥ : Subgroup G)) :
    Nat.card (G ⧸ N) + Nat.card (H.map (QuotientGroup.mk' N)) < Nat.card G + Nat.card H := by
  have hquot_lt : Nat.card (G ⧸ N) < Nat.card G := by
    exact natCard_quotient_lt_natCard_of_ne_bot N hN
  have hmap_le : Nat.card (H.map (QuotientGroup.mk' N)) ≤ Nat.card H := by
    exact Nat.le_of_dvd (Nat.card_pos (α := H))
      (Subgroup.card_map_dvd (H := H) (QuotientGroup.mk' N))
  exact Nat.add_lt_add_of_lt_of_le hquot_lt hmap_le

private theorem quotientByFittingIsNilpotent_of_mulEquiv
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (e : G ≃* H) (hnil : QuotientByFittingIsNilpotent G) :
    QuotientByFittingIsNilpotent H := by
  have hfit_map :
      (fittingSubgroup G).map e.toMonoidHom = fittingSubgroup H := by
    apply le_antisymm
    · exact
        le_sSup ⟨
          Subgroup.Normal.map (H := fittingSubgroup G) inferInstance e.toMonoidHom e.surjective,
          nilpotent_of_mulEquiv
            (G := fittingSubgroup G)
            (G' := (fittingSubgroup G).map e.toMonoidHom)
            (MulEquiv.subgroupMap e (fittingSubgroup G))⟩
    · intro x hx
      have hx' : e.symm x ∈ (fittingSubgroup H).map e.symm.toMonoidHom := by
        exact Subgroup.mem_map.mpr ⟨x, hx, by simp⟩
      have hsymm_le : (fittingSubgroup H).map e.symm.toMonoidHom ≤ fittingSubgroup G := by
        exact
          le_sSup ⟨
            Subgroup.Normal.map (H := fittingSubgroup H) inferInstance e.symm.toMonoidHom
              e.symm.surjective,
            nilpotent_of_mulEquiv
              (G := fittingSubgroup H)
              (G' := (fittingSubgroup H).map e.symm.toMonoidHom)
              (MulEquiv.subgroupMap e.symm (fittingSubgroup H))⟩
      have hxG : e.symm x ∈ fittingSubgroup G := hsymm_le hx'
      exact Subgroup.mem_map.mpr ⟨e.symm x, hxG, by simp⟩
  haveI : ((fittingSubgroup G).map e.toMonoidHom).Normal :=
    Subgroup.Normal.map (H := fittingSubgroup G) inferInstance e.toMonoidHom e.surjective
  let eQ : (G ⧸ fittingSubgroup G) ≃* (H ⧸ fittingSubgroup H) :=
    QuotientGroup.congr
      (G' := fittingSubgroup G)
      (H' := fittingSubgroup H) (e := e) hfit_map
  exact nilpotent_of_mulEquiv
    (G := G ⧸ fittingSubgroup G) (G' := H ⧸ fittingSubgroup H) (_h := hnil) eQ

private theorem quotientByFittingIsNilpotent_of_surjective
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) (hnil : QuotientByFittingIsNilpotent G) :
    QuotientByFittingIsNilpotent H := by
  have hfit_map_nil : Group.IsNilpotent ((fittingSubgroup G).map f) := by
    let φ : fittingSubgroup G →* (fittingSubgroup G).map f :=
      { toFun := fun x => ⟨f x, Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩⟩
        map_one' := by
          ext
          simp
        map_mul' := by
          intro x y
          ext
          simp }
    have hφsurj : Function.Surjective φ := by
      rintro ⟨y, hy⟩
      rcases Subgroup.mem_map.mp hy with ⟨x, hx, hxy⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      ext
      exact hxy
    letI : Group.IsNilpotent (fittingSubgroup G) := inferInstance
    exact nilpotent_of_surjective (G := fittingSubgroup G) (G' := (fittingSubgroup G).map f) φ hφsurj
  have hfit_le : (fittingSubgroup G).map f ≤ fittingSubgroup H := by
    exact le_sSup ⟨Subgroup.Normal.map (H := fittingSubgroup G) inferInstance f hf, hfit_map_nil⟩
  have hfit_comap : fittingSubgroup G ≤ (fittingSubgroup H).comap f := by
    intro x hx
    show f x ∈ fittingSubgroup H
    exact hfit_le (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  let qf : G ⧸ fittingSubgroup G →* H ⧸ fittingSubgroup H :=
    QuotientGroup.map (N := fittingSubgroup G) (M := fittingSubgroup H) f hfit_comap
  have hmkf_surj :
      Function.Surjective ((QuotientGroup.mk' (fittingSubgroup H)).comp f) := by
    intro y
    rcases QuotientGroup.mk'_surjective (N := fittingSubgroup H) y with ⟨x, rfl⟩
    rcases hf x with ⟨z, rfl⟩
    exact ⟨z, rfl⟩
  have hqf_surj : Function.Surjective qf :=
    QuotientGroup.map_surjective_of_surjective (N := fittingSubgroup G) (M := fittingSubgroup H) f
      hmkf_surj hfit_comap
  letI : Group.IsNilpotent (G ⧸ fittingSubgroup G) := hnil
  exact nilpotent_of_surjective (G := G ⧸ fittingSubgroup G) (G' := H ⧸ fittingSubgroup H) qf hqf_surj

private theorem subgroup_isNilpotent_of_le
    {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
    [Group.IsNilpotent A] (hBA : B ≤ A) : Group.IsNilpotent B := by
  exact nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (H := B) (K := A) hBA)

private def infMulEquivSubgroupOf
    {G : Type*} [Group G] (A B : Subgroup G) :
    ↥(A ⊓ B) ≃* ↥(A.subgroupOf B) where
  toFun x := ⟨⟨x.1, x.2.2⟩, x.2.1⟩
  invFun x := ⟨x.1.1, ⟨x.2, x.1.2⟩⟩
  left_inv x := by
    ext
    rfl
  right_inv x := by
    ext
    rfl
  map_mul' x y := rfl

private def subgroupOfSwapMulEquiv
    {G : Type*} [Group G] (A K : Subgroup G) :
    ↥(K.subgroupOf A) ≃* ↥(A.subgroupOf K) where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  left_inv x := by
    ext
    rfl
  right_inv x := by
    ext
    rfl
  map_mul' x y := rfl

private theorem quotientByFittingIsNilpotent_subgroupOf
    {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (hnil : QuotientByFittingIsNilpotent G) :
    QuotientByFittingIsNilpotent H := by
  let A : Subgroup H := (fittingSubgroup G).subgroupOf H
  have hA_nil : Group.IsNilpotent A := by
    let B : Subgroup G := fittingSubgroup G ⊓ H
    have hB_nil : Group.IsNilpotent B := by
      exact subgroup_isNilpotent_of_le (A := fittingSubgroup G) (B := B) inf_le_left
    let eB : B ≃* A := infMulEquivSubgroupOf (fittingSubgroup G) H
    exact nilpotent_of_mulEquiv (G := B) (G' := A) (_h := hB_nil) eB
  have hA_le_fitH : A ≤ fittingSubgroup H := by
    exact le_sSup ⟨Subgroup.Normal.subgroupOf (inferInstance : (fittingSubgroup G).Normal) H, hA_nil⟩
  let f : H →* G ⧸ fittingSubgroup G :=
    (QuotientGroup.mk' (fittingSubgroup G)).comp H.subtype
  have hker_f : f.ker = A := by
    ext x
    constructor <;> intro hx <;> simpa [f, A, QuotientGroup.eq_one_iff] using hx
  let eKer : H ⧸ A ≃* f.range :=
    (QuotientGroup.quotientMulEquivOfEq (G := H) (M := A) (N := f.ker) hker_f.symm).trans
      (QuotientGroup.quotientKerEquivRange f)
  have hquotA_nil : Group.IsNilpotent (H ⧸ A) := by
    letI : Group.IsNilpotent (G ⧸ fittingSubgroup G) := hnil
    letI : Group.IsNilpotent f.range := Subgroup.isNilpotent f.range
    exact nilpotent_of_mulEquiv (G := f.range) (G' := H ⧸ A) eKer.symm
  let π : H ⧸ A →* H ⧸ fittingSubgroup H :=
    { toFun := Subgroup.quotientMapOfLE hA_le_fitH
      map_one' := rfl
      map_mul' := by
        intro a b
        refine Quotient.inductionOn₂' a b ?_
        intro x y
        rfl }
  have hsurj : Function.Surjective (Subgroup.quotientMapOfLE hA_le_fitH) := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro x
    exact ⟨QuotientGroup.mk x, rfl⟩
  exact nilpotent_of_surjective (G := H ⧸ A) (G' := H ⧸ fittingSubgroup H)
    π (by simpa [π] using hsurj)


universe u64

public def theorem_6_4_goal
    {G : Type u64} [Group G] [Finite G] (π : Set Nat.Primes)
    (H J₁ J₂ : Subgroup G) : Prop :=
  ∃ x ∈ J₁ ⊔ J₂, IsPiSubgroup (G := G) π (J₁.conjBy x ⊔ J₂) ∧
    x ∈ Subgroup.centralizer (H : Set G)

set_option maxHeartbeats 800000 in
private theorem theorem_6_4_main
    {G : Type u64} [Group G] [Finite G] {π : Set Nat.Primes}
    {H : Subgroup G} (hHπ' : IsPiSubgroup {p | p ∉ π} H)
    {G₀ : Subgroup G} [G₀.Normal] (hG₀Hall : ∃ π₀ : Set Nat.Primes, IsHallSubgroup π₀ G₀)
    (hnil1 : QuotientByFittingIsNilpotent G₀) (hnil2 : QuotientByFittingIsNilpotent (G ⧸ G₀))
    {J₁ J₂ : Subgroup G} (hJ₁π : IsPiSubgroup π J₁) (hJ₂π : IsPiSubgroup π J₂)
    (hnorm₁ : H ≤ Subgroup.normalizer J₁) (hnorm₂ : H ≤ Subgroup.normalizer J₂)
    (hind :
      ∀ {G' : Type u64} [Group G'] [Finite G'] {π' : Set Nat.Primes}
        {H' : Subgroup G'}, IsPiSubgroup {p | p ∉ π'} H' →
        ∀ {G₀' : Subgroup G'} [G₀'.Normal],
        (∃ π₀ : Set Nat.Primes, IsHallSubgroup π₀ G₀') →
        QuotientByFittingIsNilpotent G₀' →
        QuotientByFittingIsNilpotent (G' ⧸ G₀') →
        ∀ {J₁' J₂' : Subgroup G'},
        IsPiSubgroup π' J₁' →
        IsPiSubgroup π' J₂' →
        H' ≤ Subgroup.normalizer J₁' →
        H' ≤ Subgroup.normalizer J₂' →
        Nat.card G' + Nat.card H' < Nat.card G + Nat.card H →
        theorem_6_4_goal π' H' J₁' J₂') :
    theorem_6_4_goal π H J₁ J₂ := by
  classical
  by_cases hGnontriv : Nontrivial G
  · letI : Nontrivial G := hGnontriv
    have hsolvG₀ : IsSolvable G₀ := by
      letI : Group.IsNilpotent (G₀ ⧸ fittingSubgroup G₀) := hnil1
      have hsolvFit : IsSolvable (fittingSubgroup G₀) := by infer_instance
      have hsolvQuot : IsSolvable (G₀ ⧸ fittingSubgroup G₀) := by infer_instance
      exact
        solvable_of_ker_le_range
          ((fittingSubgroup G₀).subtype)
          (QuotientGroup.mk' (fittingSubgroup G₀))
          (by
            intro x hx
            refine ⟨⟨x, ?_⟩, rfl⟩
            exact (QuotientGroup.eq_one_iff (N := fittingSubgroup G₀) (x := x)).1 hx)
    have hsolvQuot : IsSolvable (G ⧸ G₀) := by
      letI : Group.IsNilpotent ((G ⧸ G₀) ⧸ fittingSubgroup (G ⧸ G₀)) := hnil2
      have hsolvFit : IsSolvable (fittingSubgroup (G ⧸ G₀)) := by infer_instance
      have hsolvQuotFit : IsSolvable ((G ⧸ G₀) ⧸ fittingSubgroup (G ⧸ G₀)) := by infer_instance
      exact
        solvable_of_ker_le_range
          ((fittingSubgroup (G ⧸ G₀)).subtype)
          (QuotientGroup.mk' (fittingSubgroup (G ⧸ G₀)))
          (by
            intro x hx
            refine ⟨⟨x, ?_⟩, rfl⟩
            exact (QuotientGroup.eq_one_iff (N := fittingSubgroup (G ⧸ G₀)) (x := x)).1 hx)
    have hsolvG : IsSolvable G := by
      exact
        solvable_of_ker_le_range
          (G₀.subtype)
          (QuotientGroup.mk' G₀)
          (by
            intro x hx
            refine ⟨⟨x, ?_⟩, rfl⟩
            exact (QuotientGroup.eq_one_iff (N := G₀) (x := x)).1 hx)
    let L : Subgroup G := J₁ ⊔ J₂
    have hJ₁leL : J₁ ≤ L := le_sup_left
    have hJ₂leL : J₂ ≤ L := le_sup_right
    have hsolvH : IsSolvable H := by infer_instance
    have hsolvL : IsSolvable L := by infer_instance
    -- Book proof: induction on `Nat.card G + Nat.card H`.
    let M : Subgroup G := if hG₀bot : G₀ = ⊥ then ⊤ else G₀
    have hM_nontrivial : M ≠ ⊥ := by
      -- Book (6.1): `M` is nontrivial once `G ≠ 1`.
      by_cases hG₀bot : G₀ = ⊥
      · intro hMbot
        have htop_bot : (⊤ : Subgroup G) = ⊥ := by simp [M, hG₀bot] at hMbot
        exact top_ne_bot htop_bot
      · simp [M, hG₀bot]
    have hM_hall : ∃ πM : Set Nat.Primes, IsHallSubgroup πM M := by
      -- Book (6.1): `M` is a Hall subgroup of `G`.
      by_cases hG₀bot : G₀ = ⊥
      · let πM : Set Nat.Primes := {p | p.val ∣ Nat.card G}
        refine ⟨πM, ?_⟩
        simpa [M, hG₀bot, πM] using
          (isHallSubgroup_of (G := G) (π := πM) (H := (⊤ : Subgroup G))
            (hcard := by
              intro p hp
              simpa [πM] using hp)
            (hindex := by
              intro p hp_mem hp_dvd
              exact p.property.not_dvd_one (by simpa using hp_dvd)))
      · simpa [M, hG₀bot] using hG₀Hall
    have hM_nil : QuotientByFittingIsNilpotent M := by
      -- Book (6.1): `M / F(M)` is nilpotent.
      by_cases hG₀bot : G₀ = ⊥
      · subst G₀
        have hM_eq : M = ⊤ := by simp [M]
        rw [hM_eq]
        let eBot : (G ⧸ (⊥ : Subgroup G)) ≃* G := QuotientGroup.quotientBot (G := G)
        have hfit_map_bot :
            (fittingSubgroup (G ⧸ (⊥ : Subgroup G))).map eBot.toMonoidHom = fittingSubgroup G := by
          apply le_antisymm
          · exact le_sSup ⟨
              Subgroup.Normal.map (H := fittingSubgroup (G ⧸ (⊥ : Subgroup G)))
                (inferInstance : (fittingSubgroup (G ⧸ (⊥ : Subgroup G))).Normal)
                eBot.toMonoidHom eBot.surjective,
              nilpotent_of_mulEquiv
                (G := ↥(fittingSubgroup (G ⧸ (⊥ : Subgroup G))))
                (G' := ↥((fittingSubgroup (G ⧸ (⊥ : Subgroup G))).map eBot.toMonoidHom))
                (Subgroup.equivMapOfInjective
                  (f := eBot.toMonoidHom) (fittingSubgroup (G ⧸ (⊥ : Subgroup G))) eBot.injective)⟩
          · intro x hx
            refine Subgroup.mem_map.mpr ?_
            refine ⟨eBot.symm x, ?_, by simp⟩
            have hx' : eBot.symm x ∈ (fittingSubgroup G).comap eBot.toMonoidHom := by
              simpa using hx
            exact
              (le_sSup
                (show
                  (fittingSubgroup G).comap eBot.toMonoidHom ∈
                    {N : Subgroup (G ⧸ (⊥ : Subgroup G)) | N.Normal ∧ Group.IsNilpotent N} from
                  ⟨
                    (inferInstance : (fittingSubgroup G).Normal).comap eBot.toMonoidHom,
                    by
                      have hmap_eq :
                          ((fittingSubgroup G).comap eBot.toMonoidHom).map eBot.toMonoidHom =
                            fittingSubgroup G :=
                        Subgroup.map_comap_eq_self_of_surjective
                          (f := eBot.toMonoidHom) eBot.surjective (fittingSubgroup G)
                      let e :
                          ((fittingSubgroup G).comap eBot.toMonoidHom) ≃*
                            fittingSubgroup G :=
                        (MulEquiv.subgroupMap eBot ((fittingSubgroup G).comap eBot.toMonoidHom)).trans
                          (MulEquiv.subgroupCongr hmap_eq)
                      exact nilpotent_of_mulEquiv
                        (G := fittingSubgroup G)
                        (G' := (fittingSubgroup G).comap eBot.toMonoidHom)
                        (_h := (inferInstance : Group.IsNilpotent (fittingSubgroup G)))
                        e.symm
                  ⟩)) hx'
        let eNil :
            ((G ⧸ (⊥ : Subgroup G)) ⧸ fittingSubgroup (G ⧸ (⊥ : Subgroup G))) ≃*
              (G ⧸ fittingSubgroup G) :=
          QuotientGroup.congr
            (G' := fittingSubgroup (G ⧸ (⊥ : Subgroup G)))
            (H' := fittingSubgroup G) (e := eBot) hfit_map_bot
        have hnilG : Group.IsNilpotent (G ⧸ fittingSubgroup G) := by
          letI :
              Group.IsNilpotent
                (((G ⧸ (⊥ : Subgroup G)) ⧸ fittingSubgroup (G ⧸ (⊥ : Subgroup G)))) := by
            simpa [QuotientByFittingIsNilpotent] using hnil2
          exact nilpotent_of_mulEquiv
            (G := ((G ⧸ (⊥ : Subgroup G)) ⧸ fittingSubgroup (G ⧸ (⊥ : Subgroup G))))
            (G' := G ⧸ fittingSubgroup G) eNil
        let eTop : (⊤ : Subgroup G) ≃* G := Subgroup.topEquiv
        have hfit_map_top :
            (fittingSubgroup (↥(⊤ : Subgroup G))).map eTop.toMonoidHom = fittingSubgroup G := by
          apply le_antisymm
          · exact le_sSup ⟨
              Subgroup.Normal.map (H := fittingSubgroup (↥(⊤ : Subgroup G)))
                (inferInstance : (fittingSubgroup (↥(⊤ : Subgroup G))).Normal)
                eTop.toMonoidHom eTop.surjective,
              nilpotent_of_mulEquiv
                (G := ↥(fittingSubgroup (↥(⊤ : Subgroup G))))
                (G' := ↥((fittingSubgroup (↥(⊤ : Subgroup G))).map eTop.toMonoidHom))
                (Subgroup.equivMapOfInjective
                  (f := eTop.toMonoidHom) (fittingSubgroup (↥(⊤ : Subgroup G))) eTop.injective)⟩
          · intro x hx
            refine Subgroup.mem_map.mpr ?_
            refine ⟨eTop.symm x, ?_, by simp⟩
            have hx' : eTop.symm x ∈ (fittingSubgroup G).comap eTop.toMonoidHom := by
              simpa using hx
            exact
              (le_sSup
                (show
                  (fittingSubgroup G).comap eTop.toMonoidHom ∈
                    {N : Subgroup (↥(⊤ : Subgroup G)) | N.Normal ∧ Group.IsNilpotent N} from
                  ⟨
                    (inferInstance : (fittingSubgroup G).Normal).comap eTop.toMonoidHom,
                    by
                      have hmap_eq :
                          ((fittingSubgroup G).comap eTop.toMonoidHom).map eTop.toMonoidHom =
                            fittingSubgroup G :=
                        Subgroup.map_comap_eq_self_of_surjective
                          (f := eTop.toMonoidHom) eTop.surjective (fittingSubgroup G)
                      let e :
                          ((fittingSubgroup G).comap eTop.toMonoidHom) ≃*
                            fittingSubgroup G :=
                        (MulEquiv.subgroupMap eTop ((fittingSubgroup G).comap eTop.toMonoidHom)).trans
                          (MulEquiv.subgroupCongr hmap_eq)
                      exact nilpotent_of_mulEquiv
                        (G := fittingSubgroup G)
                        (G' := (fittingSubgroup G).comap eTop.toMonoidHom)
                        (_h := (inferInstance : Group.IsNilpotent (fittingSubgroup G)))
                        e.symm
                  ⟩)) hx'
        let eTopQ :
            (↥(⊤ : Subgroup G) ⧸ fittingSubgroup (↥(⊤ : Subgroup G))) ≃*
              (G ⧸ fittingSubgroup G) :=
          QuotientGroup.congr
            (G' := fittingSubgroup (↥(⊤ : Subgroup G)))
            (H' := fittingSubgroup G) (e := eTop) hfit_map_top
        letI : Group.IsNilpotent (G ⧸ fittingSubgroup G) := hnilG
        exact nilpotent_of_mulEquiv
          (G := G ⧸ fittingSubgroup G)
          (G' := ↥(⊤ : Subgroup G) ⧸ fittingSubgroup (↥(⊤ : Subgroup G)))
          eTopQ.symm
      · have hM_eq : M = G₀ := by simp [M, hG₀bot]
        rw [hM_eq]
        simpa [QuotientByFittingIsNilpotent] using hnil1
    have hHnormL : H ≤ Subgroup.normalizer L := by
      intro h hh
      have hJ₁conj : J₁.conjBy h = J₁ :=
        conjBy_eq_of_mem_normalizer_local (H := J₁) (hnorm₁ hh)
      have hJ₂conj : J₂.conjBy h = J₂ :=
        conjBy_eq_of_mem_normalizer_local (H := J₂) (hnorm₂ hh)
      have hLconj : L.conjBy h = L := by
        calc
          L.conjBy h = J₁.conjBy h ⊔ J₂.conjBy h := by
            simpa [L, Subgroup.conjBy] using
              (Subgroup.map_sup J₁ J₂ (MulAut.conj h).toMonoidHom)
          _ = J₁ ⊔ J₂ := by rw [hJ₁conj, hJ₂conj]
          _ = L := rfl
      exact mem_normalizer_of_conjBy_eq_local hLconj
    have hreduce_LH :
        L ⊔ H < ⊤ →
        ∃ x ∈ L, IsPiSubgroup (G := G) π (J₁.conjBy x ⊔ J₂) ∧
          x ∈ Subgroup.centralizer (H : Set G) := by
      intro hproper
      -- Textbook first reduction: replace `G` by `LH`.
      -- The induction hypothesis is applied to the subgroup `L ⊔ H`.
      let K : Subgroup G := L ⊔ H
      have hH_le_K : H ≤ K := le_sup_right
      have hmeasure :
          Nat.card K + Nat.card (H.subgroupOf K) < Nat.card G + Nat.card H := by
        simpa [K, natCard_subgroupOf_eq H K hH_le_K] using
          (measure_lt_of_proper_subgroup_local64 (H := H) (K := K) hproper)
      have hIH_K :
          theorem_6_4_goal π (H.subgroupOf K) (J₁.subgroupOf K) (J₂.subgroupOf K) := by
        haveI : M.Normal := by
          by_cases hG₀bot : G₀ = ⊥
          · simp [M, hG₀bot]
          · simpa [M, hG₀bot] using (inferInstance : G₀.Normal)
        haveI : (M.subgroupOf K).Normal := by
          exact Subgroup.Normal.subgroupOf (inferInstance : M.Normal) K
        have hHπ'_K : IsPiSubgroup {p | p ∉ π} (H.subgroupOf K) := by
          intro p hp
          exact hHπ' p (by
            simpa [natCard_subgroupOf_eq H K hH_le_K] using hp)
        have hG₀Hall_K : ∃ π₀ : Set Nat.Primes, IsHallSubgroup π₀ (M.subgroupOf K) := by
          rcases hM_hall with ⟨πM, hHallM⟩
          refine ⟨πM, isHallSubgroup_of (G := K) (π := πM) (H := M.subgroupOf K) ?_ ?_⟩
          · intro p hp
            let B : Subgroup M := K.subgroupOf M
            have hcard_eq : Nat.card (M.subgroupOf K) = Nat.card B := by
              simpa [B] using Nat.card_congr (subgroupOfSwapMulEquiv M K).toEquiv.symm
            have hpM : p.val ∣ Nat.card M := by
              exact dvd_trans (hcard_eq ▸ hp) (Subgroup.card_subgroup_dvd_card B)
            exact hHallM.p_in_pi_of_p_dvd_card p hpM
          · intro p hp_mem hp_idx
            have hidx_dvd : (M.subgroupOf K).index ∣ M.index := by
              simpa [Subgroup.relIndex] using
                (Subgroup.relIndex_dvd_index_of_normal (H := M) (K := K))
            exact (hHallM.p_in_pi_of_p_dvd_index p (dvd_trans hp_idx hidx_dvd)) hp_mem
        have hnil1_K : QuotientByFittingIsNilpotent (M.subgroupOf K) := by
          let B : Subgroup M := K.subgroupOf M
          have hB_nil : QuotientByFittingIsNilpotent B :=
            quotientByFittingIsNilpotent_subgroupOf (G := M) (H := B) hM_nil
          let e : B ≃* (M.subgroupOf K) := subgroupOfSwapMulEquiv M K
          exact quotientByFittingIsNilpotent_of_mulEquiv e hB_nil
        have hnil2_K : QuotientByFittingIsNilpotent (K ⧸ M.subgroupOf K) := by
          by_cases hG₀bot : G₀ = ⊥
          · have htop : (M.subgroupOf K : Subgroup K) = ⊤ := by
              simp [M, hG₀bot]
            haveI : Subsingleton (K ⧸ (M.subgroupOf K : Subgroup K)) := by
              rw [htop]
              exact QuotientGroup.subsingleton_quotient_top
            simpa [QuotientByFittingIsNilpotent, htop] using
              (inferInstance :
                Group.IsNilpotent
                  ((K ⧸ (M.subgroupOf K : Subgroup K)) ⧸ fittingSubgroup (K ⧸ (M.subgroupOf K : Subgroup K))))
          · have hM_eq : M = G₀ := by simp [M, hG₀bot]
            have hsub_eq : (M.subgroupOf K : Subgroup K) = G₀.subgroupOf K := by
              simp [M, hG₀bot]
            let qM : K →* G ⧸ G₀ := (QuotientGroup.mk' G₀).comp K.subtype
            have hker_qM : qM.ker = G₀.subgroupOf K := by
              ext x
              change qM x = 1 ↔ (x : G) ∈ G₀
              simp [qM, QuotientGroup.eq_one_iff]
            have hrange_nil : QuotientByFittingIsNilpotent qM.range :=
              quotientByFittingIsNilpotent_subgroupOf (G := G ⧸ G₀) (H := qM.range) hnil2
            let eKer0 : (K ⧸ G₀.subgroupOf K) ≃* qM.range :=
              (QuotientGroup.quotientMulEquivOfEq (G := K) (M := G₀.subgroupOf K) (N := qM.ker)
                hker_qM.symm).trans
                (QuotientGroup.quotientKerEquivRange qM)
            have hquot0 : QuotientByFittingIsNilpotent (K ⧸ G₀.subgroupOf K) :=
              quotientByFittingIsNilpotent_of_mulEquiv eKer0.symm hrange_nil
            let eEq : (K ⧸ M.subgroupOf K) ≃* (K ⧸ G₀.subgroupOf K) :=
              QuotientGroup.quotientMulEquivOfEq hsub_eq
            exact quotientByFittingIsNilpotent_of_mulEquiv eEq.symm hquot0
        have hJ₁_le_K : J₁ ≤ K := le_trans hJ₁leL le_sup_left
        have hJ₂_le_K : J₂ ≤ K := le_trans hJ₂leL le_sup_left
        have hJ₁π_K : IsPiSubgroup π (J₁.subgroupOf K) := by
          intro p hp
          exact hJ₁π p (by
            simpa [natCard_subgroupOf_eq J₁ K hJ₁_le_K] using hp)
        have hJ₂π_K : IsPiSubgroup π (J₂.subgroupOf K) := by
          intro p hp
          exact hJ₂π p (by
            simpa [natCard_subgroupOf_eq J₂ K hJ₂_le_K] using hp)
        have hnorm₁_K : H.subgroupOf K ≤ Subgroup.normalizer (J₁.subgroupOf K) := by
          intro x hx
          have hx_norm : x ∈ (Subgroup.normalizer J₁).subgroupOf K := hnorm₁ hx
          simpa [Subgroup.subgroupOf_normalizer_eq hJ₁_le_K] using hx_norm
        have hnorm₂_K : H.subgroupOf K ≤ Subgroup.normalizer (J₂.subgroupOf K) := by
          intro x hx
          have hx_norm : x ∈ (Subgroup.normalizer J₂).subgroupOf K := hnorm₂ hx
          simpa [Subgroup.subgroupOf_normalizer_eq hJ₂_le_K] using hx_norm
        exact
          hind hHπ'_K hG₀Hall_K hnil1_K hnil2_K
            hJ₁π_K hJ₂π_K hnorm₁_K hnorm₂_K hmeasure
      -- Remaining work: transport the subgroup-level conclusion from `K`
      -- back to the ambient group `G`.
      obtain ⟨x, hxL, hxpi, hxcent⟩ := hIH_K
      let xG : G := x
      have hJ₁leK : J₁ ≤ K := le_trans hJ₁leL le_sup_left
      have hJ₂leK : J₂ ≤ K := le_trans hJ₂leL le_sup_left
      have hxL_map : xG ∈ (J₁.subgroupOf K ⊔ J₂.subgroupOf K).map K.subtype := by
        exact Subgroup.mem_map.mpr ⟨x, hxL, rfl⟩
      have hsup_map :
          (J₁.subgroupOf K ⊔ J₂.subgroupOf K).map K.subtype = L := by
        calc
          (J₁.subgroupOf K ⊔ J₂.subgroupOf K).map K.subtype =
              (J₁.subgroupOf K).map K.subtype ⊔ (J₂.subgroupOf K).map K.subtype := by
                simpa using (Subgroup.map_sup (J₁.subgroupOf K) (J₂.subgroupOf K) K.subtype)
          _ = J₁ ⊔ J₂ := by simp [hJ₁leK, hJ₂leK]
          _ = L := rfl
      have hxLG : xG ∈ L := by
        simpa [hsup_map] using hxL_map
      have hconj_map :
          ((J₁.subgroupOf K).conjBy x).map K.subtype = J₁.conjBy xG := by
        simpa [Subgroup.conjBy] using
          (map_subgroupOf_map_conj_eq (K0 := K) (K := J₁) hJ₁leK (n := x))
      have hpi_map :
          (((J₁.subgroupOf K).conjBy x) ⊔ J₂.subgroupOf K).map K.subtype =
            J₁.conjBy xG ⊔ J₂ := by
        calc
          (((J₁.subgroupOf K).conjBy x) ⊔ J₂.subgroupOf K).map K.subtype =
              ((J₁.subgroupOf K).conjBy x).map K.subtype ⊔ (J₂.subgroupOf K).map K.subtype := by
                simpa using
                  (Subgroup.map_sup ((J₁.subgroupOf K).conjBy x) (J₂.subgroupOf K) K.subtype)
          _ = J₁.conjBy xG ⊔ J₂ := by simp [hconj_map, hJ₂leK]
      have hpiG : IsPiSubgroup (G := G) π (J₁.conjBy xG ⊔ J₂) := by
        let S : Subgroup K := ((J₁.subgroupOf K).conjBy x) ⊔ J₂.subgroupOf K
        have hpi_mapG : IsPiSubgroup (G := G) π (S.map K.subtype) := by
          intro p hp
          exact hxpi p (dvd_trans hp (Subgroup.card_map_dvd (H := S) K.subtype))
        simpa [S, hpi_map] using hpi_mapG
      have hxcentG : xG ∈ Subgroup.centralizer (H : Set G) := by
        rw [Subgroup.mem_centralizer_iff] at hxcent ⊢
        intro h hhH
        let hK : K := ⟨h, hH_le_K hhH⟩
        have hhK : hK ∈ H.subgroupOf K := hhH
        simpa using congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hxcent) hK hhK)
      exact ⟨xG, hxLG, hpiG, hxcentG⟩
    have hcase_eq_LH :
        L ⊔ H = ⊤ →
        ∃ x ∈ L, IsPiSubgroup (G := G) π (J₁.conjBy x ⊔ J₂) ∧
          x ∈ Subgroup.centralizer (H : Set G) := by
      intro hLH
      have h62 : ∀ K : Subgroup G, IsPiSubgroup π K → K ≤ L := by
        -- Textbook (6.2): once `G = LH`, every `π`-subgroup lies in `L`.
        intro K hKπ
        have hLH_le_norm : L ⊔ H ≤ Subgroup.normalizer (L : Set G) := sup_le L.le_normalizer hHnormL
        have hnorm_top : Subgroup.normalizer (L : Set G) = ⊤ := by
          apply top_unique
          simpa [hLH] using hLH_le_norm
        letI : L.Normal := (Subgroup.normalizer_eq_top_iff).mp hnorm_top
        let q : G →* G ⧸ L := QuotientGroup.mk' L
        have hLmap_bot : L.map q = ⊥ := by
          simp [q]
        have htop_map : (⊤ : Subgroup G).map q = ⊤ := by
          exact Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective (N := L))
        have hHmap_top : H.map q = ⊤ := by
          calc
            H.map q = L.map q ⊔ H.map q := by simp [hLmap_bot]
            _ = (L ⊔ H).map q := by
              simpa [L, sup_assoc] using (Subgroup.map_sup L H q).symm
            _ = ⊤ := by simpa [hLH] using htop_map
        have hquot_pi' : IsPiGroup {p | p ∉ π} (G ⧸ L) := by
          rw [IsPiGroup_iff]
          intro p hp
          have hp_dvd_Hmap : p.val ∣ Nat.card (H.map q) := by
            rw [hHmap_top]
            simpa using hp
          have hp_dvd_H : p.val ∣ Nat.card H :=
            dvd_trans hp_dvd_Hmap (Subgroup.card_map_dvd (H := H) q)
          exact (IsPiGroup_iff {p | p ∉ π} H).1 (IsPiSubgroup.isPiGroup (H := H) hHπ') p hp_dvd_H
        have hKbar_pi : IsPiGroup π (K.map q) := by
          rw [IsPiGroup_iff]
          intro p hp
          have hp_dvd_K : p.val ∣ Nat.card K :=
            dvd_trans hp (Subgroup.card_map_dvd (H := K) q)
          exact (IsPiGroup_iff π K).1 (IsPiSubgroup.isPiGroup (H := K) hKπ) p hp_dvd_K
        have hKbar_pi' : IsPiGroup {p | p ∉ π} (K.map q) := by
          rw [IsPiGroup_iff]
          intro p hp
          have hp_dvd_quot : p.val ∣ Nat.card (G ⧸ L) :=
            dvd_trans hp (Subgroup.card_subgroup_dvd_card (K.map q))
          exact (IsPiGroup_iff {p | p ∉ π} (G ⧸ L)).1 hquot_pi' p hp_dvd_quot
        have hKbar_card_one : Nat.card (K.map q) = 1 := by
          exact (Nat.coprime_self _).1
            (coprime_card_of_isPiGroup_compl (G := K.map q) (A := K.map q) hKbar_pi hKbar_pi')
        have hKbar_bot : K.map q = ⊥ := (Subgroup.card_eq_one (H := K.map q)).1 hKbar_card_one
        intro x hxK
        have hxbar : q x ∈ K.map q := Subgroup.mem_map.mpr ⟨x, hxK, rfl⟩
        have hxone : q x = 1 := by simp [hKbar_bot] at hxbar; simpa using hxbar
        exact (QuotientGroup.eq_one_iff (N := L) (x := x)).1 hxone
      have hcase1_main :
          (∃ p : Nat.Primes, p.val ∣ Nat.card (fittingSubgroup G) ∧ ¬ p.val ∣ Nat.card H) →
          ∃ x ∈ L, IsPiSubgroup (G := G) π (J₁.conjBy x ⊔ J₂) ∧
            x ∈ Subgroup.centralizer (H : Set G) := by
        intro hcase1
        -- Textbook case 1:
        -- choose `p`, choose a minimal normal `N ≤ O_p(F(G))`,
        -- apply induction to `G / N`, lift, then use Proposition 1.5 inside `L*`.
        obtain ⟨p, hp_fit, hp_not_H⟩ := hcase1
        letI : Fact p.1.Prime := ⟨p.2⟩
        let F : Subgroup G := fittingSubgroup G
        let P₀ : Sylow p.1 ↥F := Classical.choice (Sylow.nonempty (p := p.1) (G := ↥F))
        let P : Subgroup G := ((P₀ : Subgroup ↥F)).map F.subtype
        have hP₀_ne_bot : (P₀ : Subgroup ↥F) ≠ ⊥ := by
          exact Sylow.ne_bot_of_dvd_card P₀ (by simpa [F] using hp_fit)
        have hP_ne_bot : P ≠ ⊥ := by
          intro hP_bot
          apply hP₀_ne_bot
          exact
            (Subgroup.map_eq_bot_iff_of_injective (H := (P₀ : Subgroup ↥F)) (f := F.subtype)
              F.subtype_injective).1 (by simpa [P] using hP_bot)
        have hP_normal : P.Normal := by
          have hF_nil : Group.IsNilpotent ↥F := by
            dsimp [F]
            infer_instance
          have hP₀_normal : (P₀ : Subgroup ↥F).Normal :=
            Group.IsNilpotent.sylow_normal hF_nil p.1 P₀
          have hF_normal : F.Normal := by
            dsimp [F]
            infer_instance
          letI : F.Normal := hF_normal
          haveI : (P₀ : Subgroup ↥F).Characteristic := Sylow.characteristic_of_normal P₀ hP₀_normal
          simpa [P] using (inferInstance : (((P₀ : Subgroup ↥F)).map F.subtype).Normal)
        have hP_p : IsPGroup p.1 P := by
          simpa [P] using (P₀.isPGroup'.map F.subtype)
        have hP_le_fit : P ≤ fittingSubgroup G := by
          intro x hx
          rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
          exact y.2
        have hN_exists := exists_minimal_normal_le (G := G) P hP_normal hP_ne_bot
        let N : Subgroup G := by
          exact Classical.choose hN_exists
        have hN_normal : N.Normal := by
          exact (Classical.choose_spec hN_exists).1
        have hN_nontrivial : N ≠ ⊥ := by
          exact (Classical.choose_spec hN_exists).2.2.1
        have hN_p : IsPGroup p.1 N := by
          exact IsPGroup.to_le (H := N) (K := P) hP_p ((Classical.choose_spec hN_exists).2.1)
        have hN_le_fit : N ≤ fittingSubgroup G := by
          exact ((Classical.choose_spec hN_exists).2.1).trans hP_le_fit
        have hN_le_L : N ≤ L := by
          -- Since `G/L` is a quotient of `H` and `p` does not divide `|H|`,
          -- the image of `N` in `G/L` is trivial.
          have hLH_le_norm : L ⊔ H ≤ Subgroup.normalizer (L : Set G) := by
            exact sup_le L.le_normalizer hHnormL
          have hnorm_top : Subgroup.normalizer (L : Set G) = ⊤ := by
            apply top_unique
            simpa [hLH] using hLH_le_norm
          letI : L.Normal := (Subgroup.normalizer_eq_top_iff).mp hnorm_top
          let qL : G →* G ⧸ L := QuotientGroup.mk' L
          have hLmap_bot : L.map qL = ⊥ := by
            simp [qL]
          have htop_map : (⊤ : Subgroup G).map qL = ⊤ := by
            exact Subgroup.map_top_of_surjective qL (QuotientGroup.mk'_surjective (N := L))
          have hHmap_top : H.map qL = ⊤ := by
            calc
              H.map qL = L.map qL ⊔ H.map qL := by simp [hLmap_bot]
              _ = (L ⊔ H).map qL := by
                simpa [L, sup_assoc] using (Subgroup.map_sup L H qL).symm
              _ = ⊤ := by simpa [hLH] using htop_map
          have hp_not_dvd_quot : ¬ p.val ∣ Nat.card (G ⧸ L) := by
            intro hp_quot
            have hp_dvd_Hmap : p.val ∣ Nat.card (H.map qL) := by
              rw [hHmap_top]
              simpa using hp_quot
            exact hp_not_H (dvd_trans hp_dvd_Hmap (Subgroup.card_map_dvd (H := H) qL))
          have hNbar_p : IsPGroup p.1 (N.map qL) := by
            simpa using hN_p.map qL
          have hNbar_bot : N.map qL = ⊥ := by
            by_contra hNbar_ne_bot
            rcases (IsPGroup.iff_card.mp hNbar_p) with ⟨n, hn⟩
            have hn_ne_zero : n ≠ 0 := by
              intro hn0
              apply hNbar_ne_bot
              have hcard_one : Nat.card (N.map qL) = 1 := by
                simpa [hn0] using hn
              exact (Subgroup.card_eq_one (H := N.map qL)).1 hcard_one
            have hp_dvd_Nbar : p.val ∣ Nat.card (N.map qL) := by
              rw [hn]
              exact dvd_pow_self p.1 hn_ne_zero
            exact hp_not_dvd_quot (dvd_trans hp_dvd_Nbar (Subgroup.card_subgroup_dvd_card (N.map qL)))
          intro x hxN
          have hxbar : qL x ∈ N.map qL := Subgroup.mem_map.mpr ⟨x, hxN, rfl⟩
          have hxone : qL x = 1 := by
            simp [hNbar_bot] at hxbar
            simpa using hxbar
          exact (QuotientGroup.eq_one_iff (N := L) (x := x)).1 hxone
        let qN : G →* G ⧸ N := QuotientGroup.mk' N
        have hquot_case1 :
            ∃ y ∈ L, IsPiSubgroup (G := G ⧸ N) π ((J₁.conjBy y ⊔ J₂).map qN) ∧
              qN y ∈ Subgroup.centralizer ((H.map qN : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
          -- This is the induction step on `G / N`.
          have hmeasure_q :
              Nat.card (G ⧸ N) + Nat.card (H.map qN) < Nat.card G + Nat.card H := by
            exact measure_lt_of_quotient_local64 (N := N) (H := H) hN_nontrivial
          have hIH_q :
              theorem_6_4_goal π (H.map qN) (J₁.map qN) (J₂.map qN) := by
            haveI : (M.map qN : Subgroup (G ⧸ N)).Normal := by
              haveI : M.Normal := by
                by_cases hG₀bot : G₀ = ⊥
                · simp [M, hG₀bot]
                · simpa [M, hG₀bot] using (inferInstance : G₀.Normal)
              exact Subgroup.Normal.map (inferInstance : M.Normal) qN
                (QuotientGroup.mk'_surjective (N := N))
            have hHπ'_q : IsPiSubgroup {p | p ∉ π} (H.map qN) := by
              intro p hp
              exact hHπ' p (dvd_trans hp (Subgroup.card_map_dvd (H := H) qN))
            have hG₀Hall_q :
                ∃ π₀ : Set Nat.Primes, IsHallSubgroup π₀ ((M.map qN : Subgroup (G ⧸ N))) := by
              rcases hM_hall with ⟨πM, hHallM⟩
              refine ⟨πM, ?_⟩
              refine isHallSubgroup_of (G := G ⧸ N) (π := πM) (H := M.map qN) ?_ ?_
              · intro q hq_dvd
                exact hHallM.p_in_pi_of_p_dvd_card q (hq_dvd.trans (Subgroup.card_map_dvd (H := M) qN))
              · intro q hq_mem hq_dvd_idx
                have hidx_dvd : (M.map qN).index ∣ M.index := Subgroup.index_map_dvd (H := M)
                  (QuotientGroup.mk'_surjective (N := N))
                exact (hHallM.p_in_pi_of_p_dvd_index q (hq_dvd_idx.trans hidx_dvd)) hq_mem
            have hnil1_q : QuotientByFittingIsNilpotent (M.map qN : Subgroup (G ⧸ N)) := by
              let qM : M →* (M.map qN : Subgroup (G ⧸ N)) :=
                { toFun := fun x => ⟨qN x, Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩⟩
                  map_one' := by apply Subtype.ext; rfl
                  map_mul' := by intro x y; apply Subtype.ext; rfl }
              have hqM_surj : Function.Surjective qM := by
                rintro ⟨y, hy⟩
                rcases Subgroup.mem_map.mp hy with ⟨x, hx, hxy⟩
                refine ⟨⟨x, hx⟩, ?_⟩
                apply Subtype.ext
                exact hxy
              exact quotientByFittingIsNilpotent_of_surjective qM hqM_surj hM_nil
            have hnil2_q :
                QuotientByFittingIsNilpotent ((G ⧸ N) ⧸ (M.map qN : Subgroup (G ⧸ N))) := by
              by_cases hG₀bot : G₀ = ⊥
              · have htop : (M.map qN : Subgroup (G ⧸ N)) = ⊤ := by
                  simpa [M, hG₀bot] using
                    (Subgroup.map_top_of_surjective qN (QuotientGroup.mk'_surjective (N := N)))
                haveI : Subsingleton ((G ⧸ N) ⧸ (M.map qN : Subgroup (G ⧸ N))) := by
                  rw [htop]
                  exact QuotientGroup.subsingleton_quotient_top
                change Group.IsNilpotent
                  ((((G ⧸ N) ⧸ (M.map qN : Subgroup (G ⧸ N)))
                    ⧸ fittingSubgroup (((G ⧸ N) ⧸ (M.map qN : Subgroup (G ⧸ N))))))
                infer_instance
              · have hM_eq : M = G₀ := by simp [M, hG₀bot]
                have hmap_eq : M.map qN = G₀.map qN := by simp [hM_eq]
                haveI : (G₀.map qN : Subgroup (G ⧸ N)).Normal :=
                  Subgroup.Normal.map (inferInstance : G₀.Normal) qN
                    (QuotientGroup.mk'_surjective (N := N))
                let qG₀ : G ⧸ G₀ →* (G ⧸ N) ⧸ (G₀.map qN) :=
                  QuotientGroup.map (N := G₀) (M := G₀.map qN) qN (by
                    intro x hx
                    show qN x ∈ G₀.map qN
                    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
                have hmkq_surj :
                    Function.Surjective ((QuotientGroup.mk' (G₀.map qN)).comp qN) := by
                  intro y
                  rcases QuotientGroup.mk'_surjective (N := G₀.map qN) y with ⟨x, rfl⟩
                  rcases (QuotientGroup.mk'_surjective (N := N) x) with ⟨g, rfl⟩
                  exact ⟨g, rfl⟩
                have hqG₀_surj : Function.Surjective qG₀ :=
                  QuotientGroup.map_surjective_of_surjective (N := G₀) (M := G₀.map qN) qN
                    hmkq_surj (by
                      intro x hx
                      show qN x ∈ G₀.map qN
                      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
                have hquot0 : QuotientByFittingIsNilpotent ((G ⧸ N) ⧸ (G₀.map qN : Subgroup (G ⧸ N))) :=
                  quotientByFittingIsNilpotent_of_surjective qG₀ hqG₀_surj hnil2
                let eEq : ((G ⧸ N) ⧸ (M.map qN : Subgroup (G ⧸ N))) ≃*
                    ((G ⧸ N) ⧸ (G₀.map qN : Subgroup (G ⧸ N))) :=
                  QuotientGroup.quotientMulEquivOfEq hmap_eq
                exact quotientByFittingIsNilpotent_of_mulEquiv eEq.symm hquot0
            have hJ₁π_q : IsPiSubgroup π (J₁.map qN) := by
              intro p hp
              exact hJ₁π p (dvd_trans hp (Subgroup.card_map_dvd (H := J₁) qN))
            have hJ₂π_q : IsPiSubgroup π (J₂.map qN) := by
              intro p hp
              exact hJ₂π p (dvd_trans hp (Subgroup.card_map_dvd (H := J₂) qN))
            have hnorm₁_q : H.map qN ≤ Subgroup.normalizer (J₁.map qN) := by
              exact le_trans (Subgroup.map_mono hnorm₁) (Subgroup.le_normalizer_map (H := J₁) qN)
            have hnorm₂_q : H.map qN ≤ Subgroup.normalizer (J₂.map qN) := by
              exact le_trans (Subgroup.map_mono hnorm₂) (Subgroup.le_normalizer_map (H := J₂) qN)
            exact
              hind hHπ'_q hG₀Hall_q hnil1_q hnil2_q
                hJ₁π_q hJ₂π_q hnorm₁_q hnorm₂_q hmeasure_q
          -- Remaining work: choose a lift `y ∈ L` from the quotient witness and
          -- transport the `π`-group and centralizer conclusions back to the form used below.
          obtain ⟨xbar, hxbarL, hxbarPi, hxbarCent⟩ := hIH_q
          have hxbarLmap : xbar ∈ L.map qN := by
            simpa [L, Subgroup.map_sup] using hxbarL
          rcases Subgroup.mem_map.mp hxbarLmap with ⟨y, hyL, hybar_eq⟩
          refine ⟨y, hyL, ?_, ?_⟩
          · have hmap_conj :
                (J₁.conjBy y).map qN = (J₁.map qN).conjBy (qN y) := by
              simpa [Subgroup.conjBy] using map_mk'_map_conj_eq_local64 (N := N) (H := J₁) y
            have hsup_map :
                (J₁.conjBy y ⊔ J₂).map qN = (J₁.map qN).conjBy (qN y) ⊔ J₂.map qN := by
              calc
                (J₁.conjBy y ⊔ J₂).map qN = (J₁.conjBy y).map qN ⊔ J₂.map qN := by
                  simpa using (Subgroup.map_sup (J₁.conjBy y) J₂ qN)
                _ = (J₁.map qN).conjBy (qN y) ⊔ J₂.map qN := by rw [hmap_conj]
            simpa [hybar_eq, hsup_map] using hxbarPi
          · simpa [hybar_eq] using hxbarCent
        have hlift_case1 :
            ∃ z ∈ N, (H.conjBy (Classical.choose hquot_case1)).conjBy z = H := by
          -- Hall `p'`-subgroups of `HN` are conjugate by elements of `N`.
          classical
          let y : G := Classical.choose hquot_case1
          have hyL : y ∈ L := (Classical.choose_spec hquot_case1).1
          have hycent :
              qN y ∈ Subgroup.centralizer ((H.map qN : Subgroup (G ⧸ N)) : Set (G ⧸ N)) :=
            (Classical.choose_spec hquot_case1).2.2
          let HN : Subgroup G := H ⊔ N
          have hH_le_HN : H ≤ HN := le_sup_left
          have hN_le_HN : N ≤ HN := le_sup_right
          have hcop_N_H : Nat.Coprime (Nat.card N) (Nat.card H) := by
            exact (coprime_card_of_isPGroup_of_not_dvd (P := N) (A := H) hN_p hp_not_H).symm
          have hybar_norm :
              qN y ∈ Subgroup.normalizer (G := G ⧸ N) (H.map qN) := by
            exact centralizer_le_normalizer (H.map qN) hycent
          have hybar_conj :
              (H.map qN).conjBy (qN y) = H.map qN := by
            exact conjBy_eq_of_mem_normalizer_local (H := H.map qN) hybar_norm
          have hHy_map :
              (H.conjBy y).map qN = H.map qN := by
            calc
              (H.conjBy y).map qN
                  = (H.map qN).conjBy (qN y) := by
                      simpa [Subgroup.conjBy] using
                        (map_mk'_map_conj_eq_local64 (N := N) (H := H) y)
              _ = H.map qN := hybar_conj
          have hHy_le_HN : H.conjBy y ≤ HN := by
            intro x hxHy
            have hxbar : qN x ∈ (H.conjBy y).map qN := Subgroup.mem_map.mpr ⟨x, hxHy, rfl⟩
            have hxbar' : qN x ∈ H.map qN := by simpa [hHy_map] using hxbar
            have hxcomap : x ∈ (H.map qN).comap qN := hxbar'
            have hxsup : x ∈ H ⊔ N := by
              rw [QuotientGroup.comap_map_mk' (N := N) (H := H)] at hxcomap
              simpa [sup_comm] using hxcomap
            simpa [HN] using hxsup
          have hN_sup_Hy : N ⊔ H.conjBy y = HN := by
            apply le_antisymm
            · exact sup_le hN_le_HN hHy_le_HN
            · intro x hxHN
              have hxbarHN : qN x ∈ HN.map qN := Subgroup.mem_map.mpr ⟨x, hxHN, rfl⟩
              have hHN_map : HN.map qN = H.map qN := by
                calc
                  HN.map qN = (H ⊔ N).map qN := by rfl
                  _ = H.map qN ⊔ N.map qN := by
                        simpa using (Subgroup.map_sup H N qN)
                  _ = H.map qN := by simp [qN]
              have hxbar : qN x ∈ H.map qN := by simpa [hHN_map] using hxbarHN
              have hxbar' : qN x ∈ (H.conjBy y).map qN := by simpa [hHy_map] using hxbar
              rcases Subgroup.mem_map.mp hxbar' with ⟨h, hhHy, hhx⟩
              have hxhInvN : x * h⁻¹ ∈ N := by
                apply (QuotientGroup.eq_one_iff (N := N) (x := x * h⁻¹)).1
                calc
                  qN (x * h⁻¹) = qN x * (qN h)⁻¹ := by simp
                  _ = qN h * (qN h)⁻¹ := by rw [hhx]
                  _ = 1 := by simp
              exact
                (Subgroup.mem_sup_of_normal_left (s := N) (t := H.conjBy y) (x := x)).2
                  ⟨x * h⁻¹, hxhInvN, h, hhHy, by group⟩
          let Nsub : Subgroup HN := N.subgroupOf HN
          let Hsub : Subgroup HN := H.subgroupOf HN
          let Hysub : Subgroup HN := (H.conjBy y).subgroupOf HN
          haveI : Nsub.Normal := by
            simpa [Nsub] using
              (Subgroup.Normal.subgroupOf (H := N) (K := HN) (inferInstance : N.Normal))
          have hdisj_N_H : Disjoint Nsub Hsub := by
            rw [Subgroup.disjoint_def]
            intro x hxN hxH
            apply Subtype.ext
            exact (Subgroup.disjoint_def.mp (disjoint_iff.mpr (Subgroup.inf_eq_bot_of_coprime hcop_N_H)))
              (show ((x : HN) : G) ∈ N from hxN) (show ((x : HN) : G) ∈ H from hxH)
          have hcard_Hy : Nat.card (H.conjBy y) = Nat.card H := by
            simpa [Subgroup.conjBy] using
              (Subgroup.card_map_of_injective (K := H) (f := (MulAut.conj y).toMonoidHom)
                (hf := EquivLike.injective (MulAut.conj y)))
          have hcop_N_Hy : Nat.Coprime (Nat.card N) (Nat.card (H.conjBy y)) := by
            rw [hcard_Hy]
            exact hcop_N_H
          have hdisj_N_Hy : Disjoint Nsub Hysub := by
            rw [Subgroup.disjoint_def]
            intro x hxN hxHy
            apply Subtype.ext
            exact (Subgroup.disjoint_def.mp (disjoint_iff.mpr (Subgroup.inf_eq_bot_of_coprime hcop_N_Hy)))
              (show ((x : HN) : G) ∈ N from hxN) (show ((x : HN) : G) ∈ H.conjBy y from hxHy)
          have hsup_H : Nsub ⊔ Hsub = ⊤ := by
            calc
              Nsub ⊔ Hsub = (N ⊔ H).subgroupOf HN := by
                symm
                exact Subgroup.subgroupOf_sup (A := N) (A' := H) (B := HN) hN_le_HN hH_le_HN
              _ = HN.subgroupOf HN := by
                simp [HN, sup_comm]
              _ = ⊤ := by simp
          have hsup_Hy : Nsub ⊔ Hysub = ⊤ := by
            calc
              Nsub ⊔ Hysub = (N ⊔ H.conjBy y).subgroupOf HN := by
                symm
                exact Subgroup.subgroupOf_sup (A := N) (A' := H.conjBy y) (B := HN) hN_le_HN hHy_le_HN
              _ = HN.subgroupOf HN := by rw [hN_sup_Hy]
              _ = ⊤ := by simp
          have hmul_univ_H : ((Nsub : Set HN) * (Hsub : Set HN)) = Set.univ := by
            calc
              ((Nsub : Set HN) * (Hsub : Set HN)) = ((Nsub ⊔ Hsub : Subgroup HN) : Set HN) := by
                simpa using (Subgroup.normal_mul Nsub Hsub).symm
              _ = Set.univ := by simp [hsup_H]
          have hmul_univ_Hy : ((Nsub : Set HN) * (Hysub : Set HN)) = Set.univ := by
            calc
              ((Nsub : Set HN) * (Hysub : Set HN)) = ((Nsub ⊔ Hysub : Subgroup HN) : Set HN) := by
                simpa using (Subgroup.normal_mul Nsub Hysub).symm
              _ = Set.univ := by simp [hsup_Hy]
          have hcomp_H : Nsub.IsComplement' Hsub :=
            Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj_N_H hmul_univ_H
          have hcomp_Hy : Nsub.IsComplement' Hysub :=
            Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj_N_Hy hmul_univ_Hy
          let πH : Set Nat.Primes := {r | r.val ∣ Nat.card H}
          have hhall_H : IsHallSubgroup πH Hsub := by
            refine isHallSubgroup_of (G := HN) (π := πH) (H := Hsub) ?_ ?_
            · intro r hr_dvd
              change r.val ∣ Nat.card H
              simpa [Hsub, natCard_subgroupOf_eq H HN hH_le_HN] using hr_dvd
            · intro r hr_in hr_dvd_idx
              have hr_dvd_Nsub : r.val ∣ Nat.card Nsub := by
                simpa [hcomp_H.index_eq_card] using hr_dvd_idx
              have hr_dvd_N : r.val ∣ Nat.card N := by
                simpa [Nsub, natCard_subgroupOf_eq N HN hN_le_HN] using hr_dvd_Nsub
              exact (Nat.not_coprime_of_dvd_of_dvd r.2.one_lt hr_in hr_dvd_N) hcop_N_H.symm
          have hhall_Hy : IsHallSubgroup πH Hysub := by
            refine isHallSubgroup_of (G := HN) (π := πH) (H := Hysub) ?_ ?_
            · intro r hr_dvd
              change r.val ∣ Nat.card H
              rw [← hcard_Hy]
              simpa [Hysub, natCard_subgroupOf_eq (H.conjBy y) HN hHy_le_HN] using hr_dvd
            · intro r hr_in hr_dvd_idx
              have hr_dvd_Nsub : r.val ∣ Nat.card Nsub := by
                simpa [hcomp_Hy.index_eq_card] using hr_dvd_idx
              have hr_dvd_N : r.val ∣ Nat.card N := by
                simpa [Nsub, natCard_subgroupOf_eq N HN hN_le_HN] using hr_dvd_Nsub
              change r.val ∣ Nat.card H at hr_in
              have hr_in_Hy : r.val ∣ Nat.card (H.conjBy y) := by
                rwa [hcard_Hy]
              exact (Nat.not_coprime_of_dvd_of_dvd r.2.one_lt hr_in_Hy hr_dvd_N)
                (Nat.Coprime.symm hcop_N_Hy)
          have hsolvHN : IsSolvable HN := by infer_instance
          obtain ⟨w0, hw0⟩ :=
            exists_conj_eq_of_isHallSubgroup_of_solvable (G := HN) hsolvHN hhall_H hhall_Hy
          have hw0_sup : w0 ∈ Nsub ⊔ Hsub := by simp [hsup_H]
          obtain ⟨n, hnNsub, h, hhHsub, hnh_eq⟩ :=
            (Subgroup.mem_sup_of_normal_left (s := Nsub) (t := Hsub) (x := w0)).1 hw0_sup
          have hhN : h ∈ Subgroup.normalizer (G := HN) Hsub := Subgroup.le_normalizer hhHsub
          have hh_conj : Hsub.conjBy h = Hsub :=
            conjBy_eq_of_mem_normalizer_local (H := Hsub) hhN
          have hn : Hysub = Hsub.map (MulAut.conj n).toMonoidHom := by
            calc
              Hysub = Hsub.map (MulAut.conj w0).toMonoidHom := hw0
              _ = Hsub.map (MulAut.conj (n * h)).toMonoidHom := by rw [hnh_eq]
              _ = (Hsub.conjBy h).conjBy n := by
                    simpa [Subgroup.conjBy] using (Subgroup.conjBy_mul Hsub n h)
              _ = Hsub.conjBy n := by rw [hh_conj]
              _ = Hsub.map (MulAut.conj n).toMonoidHom := rfl
          have hHsub_map : Hsub.map HN.subtype = H := by
            calc
              Hsub.map HN.subtype = H ⊓ HN := by simp [Hsub]
              _ = H := inf_eq_left.mpr hH_le_HN
          have hHysub_map : Hysub.map HN.subtype = H.conjBy y := by
            calc
              Hysub.map HN.subtype = H.conjBy y ⊓ HN := by simp [Hysub]
              _ = H.conjBy y := inf_eq_left.mpr hHy_le_HN
          have hmap_hn := congrArg (fun S : Subgroup HN => S.map HN.subtype) hn
          have hy_eq_hn : H.conjBy y = H.map (MulAut.conj ((n : HN) : G)).toMonoidHom := by
            calc
              H.conjBy y = Hysub.map HN.subtype := by symm; exact hHysub_map
              _ = (Hsub.map (MulAut.conj n).toMonoidHom).map HN.subtype := by rw [hn]
              _ = H.map (MulAut.conj ((n : HN) : G)).toMonoidHom := by
                    simpa [hHsub_map] using
                      (map_subgroupOf_map_conj_eq (K0 := HN) (K := H) hH_le_HN (n := n))
          refine ⟨((n : HN) : G)⁻¹, ?_, ?_⟩
          · exact N.inv_mem hnNsub
          · calc
              (H.conjBy y).conjBy (((n : HN) : G)⁻¹)
                  = H.conjBy (((n : HN) : G)⁻¹ * y) := by
                      symm
                      simpa using (Subgroup.conjBy_mul H (((n : HN) : G)⁻¹) y)
              _ = H := Subgroup.conjBy_inv_mul_cancel (H := H) (a := ((n : HN) : G)) (b := y) hy_eq_hn.symm
        have hfinish_case1 :
            ∃ x ∈ L, IsPiSubgroup (G := G) π (J₁.conjBy x ⊔ J₂) ∧
              x ∈ Subgroup.centralizer (H : Set G) := by
          -- Set `L* = ⟨J₁^y, J₂⟩N`, then apply Proposition 1.5 inside `L*`.
          classical
          let y : G := Classical.choose hquot_case1
          have hyL : y ∈ L := (Classical.choose_spec hquot_case1).1
          have hyPi :
              IsPiSubgroup (G := G ⧸ N) π ((J₁.conjBy y ⊔ J₂).map qN) :=
            (Classical.choose_spec hquot_case1).2.1
          have hycent :
              qN y ∈ Subgroup.centralizer ((H.map qN : Subgroup (G ⧸ N)) : Set (G ⧸ N)) :=
            (Classical.choose_spec hquot_case1).2.2
          rcases hlift_case1 with ⟨z, hzN, hzH⟩
          have hcop_N_H : Nat.Coprime (Nat.card N) (Nat.card H) := by
            exact (coprime_card_of_isPGroup_of_not_dvd (P := N) (A := H) hN_p hp_not_H).symm
          have hHN_bot : H ⊓ N = ⊥ := by
            exact Subgroup.inf_eq_bot_of_coprime hcop_N_H.symm
          let x0 : G := z * y
          have hx0L : x0 ∈ L := by
            exact L.mul_mem (hN_le_L hzN) hyL
          have hx0conj : H.conjBy x0 = H := by
            calc
              H.conjBy x0 = (H.conjBy y).conjBy z := by
                simpa [x0] using (Subgroup.conjBy_mul H z y)
              _ = H := hzH
          have hzbar : qN z = 1 := by
            exact (QuotientGroup.eq_one_iff (N := N) (x := z)).2 hzN
          have hx0bar_eq : qN x0 = qN y := by
            simp [x0, hzbar]
          have hx0bar_cent :
              qN x0 ∈ Subgroup.centralizer ((H.map qN : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
            rw [hx0bar_eq]
            exact hycent
          have hx0cent : x0 ∈ Subgroup.centralizer (H : Set G) := by
            rw [Subgroup.mem_centralizer_iff]
            intro h hhH
            have hx0hH : x0 * h * x0⁻¹ ∈ H := by
              have : x0 * h * x0⁻¹ ∈ H.conjBy x0 := by
                exact Subgroup.mem_map.mpr ⟨h, hhH, rfl⟩
              simpa [hx0conj] using this
            have hcommbar : qN x0 * qN h = qN h * qN x0 := by
              exact
                ((Subgroup.mem_centralizer_iff.mp hx0bar_cent) (qN h)
                  (Subgroup.mem_map.mpr ⟨h, hhH, rfl⟩)).symm
            have hconjbar : qN (x0 * h * x0⁻¹) = qN h := by
              calc
                qN (x0 * h * x0⁻¹) = qN x0 * qN h * (qN x0)⁻¹ := by
                  simp [mul_assoc]
                _ = qN h * qN x0 * (qN x0)⁻¹ := by rw [hcommbar]
                _ = qN h := by simp
            have hcommN : x0 * h * x0⁻¹ * h⁻¹ ∈ N := by
              apply (QuotientGroup.eq_one_iff (N := N) (x := x0 * h * x0⁻¹ * h⁻¹)).mp
              calc
                qN (x0 * h * x0⁻¹ * h⁻¹) = qN (x0 * h * x0⁻¹) * (qN h)⁻¹ := by
                  simp [mul_assoc]
                _ = qN h * (qN h)⁻¹ := by rw [hconjbar]
                _ = 1 := by simp
            have hcommH : x0 * h * x0⁻¹ * h⁻¹ ∈ H := by
              exact H.mul_mem hx0hH (H.inv_mem hhH)
            have hcomm1 : x0 * h * x0⁻¹ * h⁻¹ = 1 := by
              have : x0 * h * x0⁻¹ * h⁻¹ ∈ H ⊓ N := ⟨hcommH, hcommN⟩
              have : x0 * h * x0⁻¹ * h⁻¹ ∈ (⊥ : Subgroup G) := by
                simpa [hHN_bot] using this
              simpa using this
            have hmul :
                (x0 * h * x0⁻¹ * h⁻¹) * (h * x0) = x0 * h := by
              calc
                (x0 * h * x0⁻¹ * h⁻¹) * (h * x0)
                    = x0 * h * (x0⁻¹ * (h⁻¹ * (h * x0))) := by simp [mul_assoc]
                _ = x0 * h := by simp
            calc
              h * x0 = 1 * (h * x0) := by simp
              _ = (x0 * h * x0⁻¹ * h⁻¹) * (h * x0) := by rw [hcomm1]
              _ = x0 * h := hmul
          let S : Subgroup G := J₁.conjBy x0 ⊔ J₂
          let Lstar : Subgroup G := S ⊔ N
          have hS_le_L : S ≤ L := by
            refine sup_le ?_ hJ₂leL
            intro x hx
            rcases Subgroup.mem_map.mp hx with ⟨y, hyJ₁, rfl⟩
            simpa [mul_assoc] using L.mul_mem (L.mul_mem hx0L (hJ₁leL hyJ₁)) (L.inv_mem hx0L)
          have hLstar_le_L : Lstar ≤ L := sup_le hS_le_L hN_le_L
          have hJ₁leS : J₁.conjBy x0 ≤ S := le_sup_left
          have hJ₂leS : J₂ ≤ S := le_sup_right
          have hJ₁x0_pi : IsPiSubgroup (G := G) π (J₁.conjBy x0) := by
            intro r hr
            exact hJ₁π r (dvd_trans hr (Subgroup.card_map_dvd (H := J₁) (MulAut.conj x0).toMonoidHom))
          have hSmap_eq :
              S.map qN = (J₁.conjBy y ⊔ J₂).map qN := by
            have hmap_conj_x0 :
                (J₁.conjBy x0).map qN = (J₁.map qN).conjBy (qN x0) := by
              simpa [Subgroup.conjBy] using map_mk'_map_conj_eq_local64 (N := N) (H := J₁) x0
            have hmap_conj_y :
                (J₁.conjBy y).map qN = (J₁.map qN).conjBy (qN y) := by
              simpa [Subgroup.conjBy] using map_mk'_map_conj_eq_local64 (N := N) (H := J₁) y
            calc
              S.map qN = (J₁.conjBy x0).map qN ⊔ J₂.map qN := by
                simp [S, Subgroup.map_sup]
              _ = (J₁.map qN).conjBy (qN x0) ⊔ J₂.map qN := by rw [hmap_conj_x0]
              _ = (J₁.map qN).conjBy (qN y) ⊔ J₂.map qN := by rw [hx0bar_eq]
              _ = (J₁.conjBy y).map qN ⊔ J₂.map qN := by rw [hmap_conj_y]
              _ = (J₁.conjBy y ⊔ J₂).map qN := by
                symm
                simp [Subgroup.map_sup]
          have hSmap_pi : IsPiSubgroup (G := G ⧸ N) π (S.map qN) := by
            simpa [hSmap_eq] using hyPi
          have hHnorm_J₁x0 : H ≤ Subgroup.normalizer (J₁.conjBy x0) := by
            refine subgroup_le_normalizer_of_conj_mem (J₁.conjBy x0) H ?_
            intro h x hx
            have hhcent : h * x0 = x0 * h := by
              exact Subgroup.mem_centralizer_iff.mp hx0cent h h.property
            rcases Subgroup.mem_map.mp hx with ⟨u, huJ₁, rfl⟩
            have hhu : h * u * h⁻¹ ∈ J₁ := by
              exact ((Subgroup.mem_normalizer_iff.mp (hnorm₁ h.property)) u).1 huJ₁
            refine Subgroup.mem_map.mpr ?_
            refine ⟨h * u * h⁻¹, hhu, ?_⟩
            have hhcent_inv : h⁻¹ * x0⁻¹ = x0⁻¹ * h⁻¹ := by
              calc
                h⁻¹ * x0⁻¹ = (x0 * h)⁻¹ := by simp [mul_inv_rev]
                _ = (h * x0)⁻¹ := by rw [hhcent]
                _ = x0⁻¹ * h⁻¹ := by simp [mul_inv_rev]
            calc
              x0 * (h * u * h⁻¹) * x0⁻¹ = x0 * h * u * h⁻¹ * x0⁻¹ := by simp [mul_assoc]
              _ = h * x0 * u * h⁻¹ * x0⁻¹ := by rw [hhcent.symm]
              _ = h * (x0 * (u * (h⁻¹ * x0⁻¹))) := by simp [mul_assoc]
              _ = h * (x0 * (u * (x0⁻¹ * h⁻¹))) := by rw [hhcent_inv]
              _ = h * (MulAut.conj x0 u) * h⁻¹ := by simp [MulAut.conj_apply, mul_assoc]
          have hHnorm_S : H ≤ Subgroup.normalizer S := by
            intro h hh
            have hJ₁x0_conj : (J₁.conjBy x0).conjBy h = J₁.conjBy x0 := by
              exact conjBy_eq_of_mem_normalizer_local (H := J₁.conjBy x0) (hHnorm_J₁x0 hh)
            have hJ₂_conj : J₂.conjBy h = J₂ := by
              exact conjBy_eq_of_mem_normalizer_local (H := J₂) (hnorm₂ hh)
            have hSconj : S.conjBy h = S := by
              calc
                S.conjBy h = (J₁.conjBy x0).conjBy h ⊔ J₂.conjBy h := by
                  simpa [S, Subgroup.conjBy] using
                    (Subgroup.map_sup (J₁.conjBy x0) J₂ (MulAut.conj h).toMonoidHom)
                _ = S := by rw [hJ₁x0_conj, hJ₂_conj]
            exact mem_normalizer_of_conjBy_eq_local hSconj
          have hHnorm_Lstar : H ≤ Subgroup.normalizer Lstar := by
            intro h hh
            have hSconj : S.conjBy h = S := by
              exact conjBy_eq_of_mem_normalizer_local (H := S) (hHnorm_S hh)
            have hNconj : N.conjBy h = N := by
              exact conjBy_eq_of_mem_normalizer_local (H := N)
                ((Subgroup.le_normalizer_of_normal (H := N)) hh)
            have hLstarconj : Lstar.conjBy h = Lstar := by
              calc
                Lstar.conjBy h = S.conjBy h ⊔ N.conjBy h := by
                  simpa [Lstar, Subgroup.conjBy] using
                    (Subgroup.map_sup S N (MulAut.conj h).toMonoidHom)
                _ = Lstar := by rw [hSconj, hNconj]
            exact mem_normalizer_of_conjBy_eq_local hLstarconj
          letI : MulDistribMulAction ↥H ↥Lstar :=
            Subgroup.conjMulDistribMulActionOfLeNormalizer (G := G) H Lstar hHnorm_Lstar
          haveI : IsInvariant ↥H ↥Lstar ((J₁.conjBy x0).subgroupOf Lstar) := by
            refine ⟨?_⟩
            intro h g
            simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hHnorm_Lstar] using
              ((Subgroup.mem_normalizer_iff.mp (hHnorm_J₁x0 h.property)) ((g : Lstar) : G))
          haveI : IsInvariant ↥H ↥Lstar (J₂.subgroupOf Lstar) := by
            refine ⟨?_⟩
            intro h g
            simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hHnorm_Lstar] using
              ((Subgroup.mem_normalizer_iff.mp (hnorm₂ h.property)) ((g : Lstar) : G))
          have hJ₁x0_pi_sub : IsPiSubgroup (G := Lstar) π ((J₁.conjBy x0).subgroupOf Lstar) := by
            intro r hr
            exact hJ₁x0_pi r (by
              simpa [natCard_subgroupOf_eq (J₁.conjBy x0) Lstar (le_trans hJ₁leS le_sup_left)] using hr)
          have hJ₂_pi_sub : IsPiSubgroup (G := Lstar) π (J₂.subgroupOf Lstar) := by
            intro r hr
            exact hJ₂π r (by
              simpa [natCard_subgroupOf_eq J₂ Lstar (le_trans hJ₂leS le_sup_left)] using hr)
          have hJ₂_le_Lstar : J₂ ≤ Lstar := le_trans hJ₂leS le_sup_left
          have hLstar_map_eq : Lstar.map qN = S.map qN := by
            calc
              Lstar.map qN = (S ⊔ N).map qN := by rfl
              _ = S.map qN ⊔ N.map qN := by simpa using (Subgroup.map_sup S N qN)
              _ = S.map qN := by simp [qN]
          have hLstar_map_pi : IsPiSubgroup (G := G ⧸ N) π (Lstar.map qN) := by
            simpa [hLstar_map_eq] using hSmap_pi
          have hLstar_quot_pi : IsPiGroup π (↥Lstar ⧸ N.subgroupOf Lstar) := by
            let e : (↥Lstar ⧸ N.subgroupOf Lstar) ≃* Lstar.map qN := by
              simpa [qN] using (quotientSubgroupRangeEquiv Lstar N)
            exact IsPiGroup.of_injective
              (G := ↥Lstar ⧸ N.subgroupOf Lstar) (H := Lstar.map qN)
              (IsPiSubgroup.isPiGroup (H := Lstar.map qN) hLstar_map_pi)
              e.toMonoidHom e.injective
          have hcop_H_Lstar : Nat.Coprime (Nat.card H) (Nat.card Lstar) := by
            refine Nat.coprime_of_dvd ?_
            intro r hr_prime hr_dvd_H hr_dvd_Lstar
            let r' : Nat.Primes := ⟨r, hr_prime⟩
            have hr_not_quot : ¬ r ∣ Nat.card (↥Lstar ⧸ N.subgroupOf Lstar) := by
              intro hr_dvd_quot
              have hr_in_pi : r' ∈ π :=
                (IsPiGroup_iff π (↥Lstar ⧸ N.subgroupOf Lstar)).1 hLstar_quot_pi r' hr_dvd_quot
              have hr_not_pi : r' ∉ π :=
                (IsPiGroup_iff {p | p ∉ π} H).1 (IsPiSubgroup.isPiGroup (H := H) hHπ') r' hr_dvd_H
              exact hr_not_pi hr_in_pi
            rcases (r'.2.dvd_mul).mp (by
              rw [← (N.subgroupOf Lstar).card_mul_index, (N.subgroupOf Lstar).index_eq_card] at hr_dvd_Lstar
              exact hr_dvd_Lstar) with hr_dvd_Nsub | hr_dvd_quot
            · have hr_dvd_N : r ∣ Nat.card N := by
                simpa [natCard_subgroupOf_eq N Lstar le_sup_right] using hr_dvd_Nsub
              exact (Nat.not_coprime_of_dvd_of_dvd r'.2.one_lt hr_dvd_H hr_dvd_N) hcop_N_H.symm
            · exact hr_not_quot hr_dvd_quot
          have hLstar_solv : IsSolvable Lstar := by infer_instance
          obtain ⟨P₁, hP₁_hall, hP₁_inv, hJ₁_le_P₁⟩ :=
            proposition_1_5_b (G := Lstar) (A := ↥H) hLstar_solv
              (by simpa using hcop_H_Lstar) π
              ((J₁.conjBy x0).subgroupOf Lstar) hJ₁x0_pi_sub inferInstance
          obtain ⟨P₂, hP₂_hall, hP₂_inv, hJ₂_le_P₂⟩ :=
            proposition_1_5_b (G := Lstar) (A := ↥H) hLstar_solv
              (by simpa using hcop_H_Lstar) π
              (J₂.subgroupOf Lstar) hJ₂_pi_sub inferInstance
          obtain ⟨w, hw_fix, hw_conj⟩ :=
            proposition_1_5_c (G := Lstar) (A := ↥H) hLstar_solv
              (by simpa using hcop_H_Lstar) π
              P₁ P₂ hP₁_hall hP₂_hall hP₁_inv hP₂_inv
          have hw_fix_eq :
              fixedPointSubgroup (↥H) (↥Lstar) = (subgroupCentralizerIn Lstar H).subgroupOf Lstar := by
            simpa using fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn Lstar H hHnorm_Lstar
          have hw_cent_sub : w ∈ (subgroupCentralizerIn Lstar H).subgroupOf Lstar := by
            simpa [hw_fix_eq] using hw_fix
          have hw_cent : ((w : Lstar) : G) ∈ Subgroup.centralizer (H : Set G) := by
            exact hw_cent_sub.2
          have hP₂_map_pi : IsPiSubgroup (G := G) π (P₂.map Lstar.subtype) := by
            intro r hr
            exact hP₂_hall.p_in_pi_of_p_dvd_card r (dvd_trans hr (Subgroup.card_map_dvd (H := P₂) Lstar.subtype))
          have hJ₁wx0_le :
              J₁.conjBy (((w : Lstar) : G) * x0) ≤ P₂.map Lstar.subtype := by
            have htmp :
                ((J₁.conjBy x0).subgroupOf Lstar).map (MulAut.conj w).toMonoidHom ≤ P₂ := by
              calc
                ((J₁.conjBy x0).subgroupOf Lstar).map (MulAut.conj w).toMonoidHom
                    ≤ P₁.map (MulAut.conj w).toMonoidHom := by
                        exact Subgroup.map_mono hJ₁_le_P₁
                _ = P₂ := hw_conj.symm
            have htmp_map :
                ((((J₁.conjBy x0).subgroupOf Lstar).map (MulAut.conj w).toMonoidHom).map Lstar.subtype)
                  ≤ P₂.map Lstar.subtype := by
              exact Subgroup.map_mono htmp
            have hmap_eq :
                ((((J₁.conjBy x0).subgroupOf Lstar).map (MulAut.conj w).toMonoidHom).map Lstar.subtype)
                  = J₁.conjBy (((w : Lstar) : G) * x0) := by
              calc
                ((((J₁.conjBy x0).subgroupOf Lstar).map (MulAut.conj w).toMonoidHom).map Lstar.subtype)
                    = (J₁.conjBy x0).map (MulAut.conj ((w : Lstar) : G)).toMonoidHom := by
                        simpa using
                          (map_subgroupOf_map_conj_eq
                            (K0 := Lstar) (K := J₁.conjBy x0)
                            (le_trans hJ₁leS le_sup_left) (n := w))
                _ = (J₁.conjBy x0).conjBy ((w : Lstar) : G) := rfl
                _ = J₁.conjBy (((w : Lstar) : G) * x0) := by
                    symm
                    simpa using (Subgroup.conjBy_mul J₁ ((w : Lstar) : G) x0)
            rw [hmap_eq] at htmp_map
            exact htmp_map
          have hJ₂_le :
              J₂ ≤ P₂.map Lstar.subtype := by
            have htmp_map :
                (J₂.subgroupOf Lstar).map Lstar.subtype ≤ P₂.map Lstar.subtype := by
              exact Subgroup.map_mono hJ₂_le_P₂
            simpa [hJ₂_le_Lstar, inf_eq_left] using htmp_map
          refine ⟨((w : Lstar) : G) * x0, L.mul_mem (hLstar_le_L w.property) hx0L, ?_, ?_⟩
          · have hsup_le :
                J₁.conjBy (((w : Lstar) : G) * x0) ⊔ J₂ ≤ P₂.map Lstar.subtype := by
              exact sup_le hJ₁wx0_le hJ₂_le
            intro r hr
            exact hP₂_map_pi r (dvd_trans hr (Subgroup.card_dvd_of_le hsup_le))
          · rw [Subgroup.mem_centralizer_iff] at hx0cent hw_cent ⊢
            intro h hhH
            calc
              h * (((w : Lstar) : G) * x0) = (h * ((w : Lstar) : G)) * x0 := by simp [mul_assoc]
              _ = (((w : Lstar) : G) * h) * x0 := by rw [hw_cent h hhH]
              _ = ((w : Lstar) : G) * (h * x0) := by simp [mul_assoc]
              _ = ((w : Lstar) : G) * (x0 * h) := by rw [hx0cent h hhH]
              _ = (((w : Lstar) : G) * x0) * h := by simp [mul_assoc]
        exact hfinish_case1
      have hcase2_main :
          (∀ p : Nat.Primes, p.val ∣ Nat.card (fittingSubgroup G) → p.val ∣ Nat.card H) →
          ∃ x ∈ L, IsPiSubgroup (G := G) π (J₁.conjBy x ⊔ J₂) ∧
            x ∈ Subgroup.centralizer (H : Set G) := by
        intro hcase2
        let B : Subgroup G := H ⊓ M
        have hB_le_H : B ≤ H := inf_le_left
        have hB_le_M : B ≤ M := inf_le_right
        have hB_pi' : IsPiSubgroup {p | p ∉ π} B := by
          intro p hp
          exact hHπ' p (dvd_trans hp (Subgroup.card_dvd_of_le hB_le_H))
        haveI : M.Normal := by
          by_cases hG₀bot : G₀ = ⊥
          · simp [M, hG₀bot]
          · simpa [M, hG₀bot] using (inferInstance : G₀.Normal)
        let Bsub : Subgroup H := M.comap H.subtype
        have hBsub_map : Bsub.map H.subtype = B := by
          ext x
          constructor
          · intro hx
            rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
            exact ⟨y.2, hy⟩
          · intro hx
            exact Subgroup.mem_map.mpr ⟨⟨x, hx.1⟩, hx.2, rfl⟩
        have hBsub_card : Nat.card Bsub = Nat.card B := by
          calc
            Nat.card Bsub = Nat.card (Bsub.map H.subtype) := by
              symm
              exact
                Subgroup.card_map_of_injective (K := Bsub) (f := H.subtype)
                  H.subtype_injective
            _ = Nat.card B := by rw [hBsub_map]
        have hBsub_index_dvd : Bsub.index ∣ M.index := by
          let qHM : H →* G ⧸ M := (QuotientGroup.mk' M).comp H.subtype
          have hker_qHM : qHM.ker = Bsub := by
            ext x
            change QuotientGroup.mk' M (x : G) = 1 ↔ x ∈ Bsub
            constructor
            · intro hx
              exact (QuotientGroup.eq_one_iff (N := M) (x := (x : G))).1 hx
            · intro hx
              exact (QuotientGroup.eq_one_iff (N := M) (x := (x : G))).2 hx
          rw [← hker_qHM, Subgroup.index_ker]
          simpa [Subgroup.index_eq_card] using
            (Subgroup.card_subgroup_dvd_card qHM.range)
        rcases hM_hall with ⟨πM, hHallM⟩
        have hBsub_cop : Nat.Coprime (Nat.card Bsub) Bsub.index := by
          apply Nat.coprime_of_dvd'
          intro k hk hk_card hk_idx
          let p : Nat.Primes := ⟨k, hk⟩
          have hp_card_B : p.val ∣ Nat.card B := by
            simpa [p, hBsub_card] using hk_card
          have hp_card_M : p.val ∣ Nat.card M := by
            exact dvd_trans hp_card_B (Subgroup.card_dvd_of_le hB_le_M)
          have hp_mem : p ∈ πM := hHallM.p_in_pi_of_p_dvd_card p hp_card_M
          have hp_not_mem : p ∉ πM :=
            hHallM.p_in_pi_of_p_dvd_index p (dvd_trans hk_idx hBsub_index_dvd)
          exact False.elim (hp_not_mem hp_mem)
        obtain ⟨Hstar, hcompB⟩ :=
          Subgroup.exists_right_complement'_of_coprime (N := Bsub) hBsub_cop
        let HstarG : Subgroup G := Hstar.map H.subtype
        have hHstarG_le_H : HstarG ≤ H := by
          intro x hx
          rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
          exact y.2
        have hHstar_pi' : IsPiSubgroup {p | p ∉ π} HstarG := by
          intro p hp
          exact hHπ' p (dvd_trans hp (Subgroup.card_dvd_of_le hHstarG_le_H))
        have hHstar_norm₁ : HstarG ≤ Subgroup.normalizer J₁ := by
          exact hHstarG_le_H.trans hnorm₁
        have hHstar_norm₂ : HstarG ≤ Subgroup.normalizer J₂ := by
          exact hHstarG_le_H.trans hnorm₂
        -- Textbook case 2:
        -- derive local (6.4), choose a nontrivial Hall subgroup `B ≤ H ∩ M`,
        -- pass to a complement `H*`, apply induction on smaller `H*`,
        -- and then show `B` centralizes `L`.
        -- The remaining hard point is to show that `B` centralizes `L`, obtain
        -- a strict-cardinality induction step for `HstarG`, and combine the
        -- induction witness for `HstarG` with the complement decomposition
        -- `H = B ⋊ Hstar`.
        have hHstarG_card : Nat.card HstarG = Nat.card Hstar := by
          exact
            Subgroup.card_map_of_injective (K := Hstar) (f := H.subtype)
              H.subtype_injective
        have hHstarG_lt : Nat.card HstarG < Nat.card H := by
          -- This is the formal version of the textbook claim `|H*| < |H|`,
          -- which uses that `B = H ∩ M` is nontrivial in case 2.
          have hfitM_ne_bot : fittingSubgroup M ≠ ⊥ := by
            letI : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot M).2 hM_nontrivial
            obtain ⟨N, hNnorm, hN_le_top, hN_ne_bot, hNmin⟩ :=
              exists_minimal_normal_le (G := M) (⊤ : Subgroup M) inferInstance top_ne_bot
            letI : IsMinimalNormal N := {
              minimal := by
                intro K hKnorm hKN
                by_cases hK_bot : K = ⊥
                · exact Or.inl hK_bot
                · exact Or.inr (hNmin K hKnorm hKN hK_bot)
            }
            have hN_center :
                N ≤ centerIn (G := M) (fittingSubgroup M) :=
              minimalNormal_solvable_le_centerIn_fittingSubgroup (G := M) N
            have hN_le_fitM : N ≤ fittingSubgroup M := by
              intro x hx
              exact (hN_center hx).1
            intro hfitM_bot
            have hN_bot : N = ⊥ := by
              apply le_bot_iff.mp
              simpa [hfitM_bot] using hN_le_fitM
            exact hN_ne_bot hN_bot
          let FMG : Subgroup G := (fittingSubgroup M).map M.subtype
          have hFMG_card :
              Nat.card FMG = Nat.card (fittingSubgroup M) := by
            dsimp [FMG]
            exact
              Subgroup.card_map_of_injective (K := fittingSubgroup M) (f := M.subtype)
                M.subtype_injective
          have hFMG_nil : Group.IsNilpotent FMG := by
            dsimp [FMG]
            let e :
                fittingSubgroup M ≃* (fittingSubgroup M).map M.subtype :=
              Subgroup.equivMapOfInjective (f := M.subtype) (fittingSubgroup M) M.subtype_injective
            exact
              nilpotent_of_mulEquiv (G := fittingSubgroup M)
                (G' := (fittingSubgroup M).map M.subtype) e
          have hFMG_le_fitG : FMG ≤ fittingSubgroup G := by
            exact
              le_sSup ⟨
                (inferInstance : FMG.Normal),
                hFMG_nil
              ⟩
          have hfitM_card_gt : 1 < Nat.card (fittingSubgroup M) :=
            (Subgroup.one_lt_card_iff_ne_bot (H := fittingSubgroup M)).2 hfitM_ne_bot
          have hfitM_card_ne_one : Nat.card (fittingSubgroup M) ≠ 1 := by
            exact Nat.ne_of_gt hfitM_card_gt
          obtain ⟨p, hpprime, hp_fitM_card⟩ :=
            Nat.exists_prime_and_dvd hfitM_card_ne_one
          let q : Nat.Primes := ⟨p, hpprime⟩
          have hq_fitM_card : q.val ∣ Nat.card (fittingSubgroup M) := by
            simpa [q] using hp_fitM_card
          have hq_M_card : q.val ∣ Nat.card M := by
            exact dvd_trans hq_fitM_card (Subgroup.card_subgroup_dvd_card (fittingSubgroup M))
          have hq_FMG_card : q.val ∣ Nat.card FMG := by
            simpa [hFMG_card] using hq_fitM_card
          have hq_fitG_card : q.val ∣ Nat.card (fittingSubgroup G) := by
            exact dvd_trans hq_FMG_card (Subgroup.card_dvd_of_le hFMG_le_fitG)
          have hq_H_card : q.val ∣ Nat.card H := hcase2 q hq_fitG_card
          have hBsub_ne_bot : Bsub ≠ ⊥ := by
            intro hBsub_bot
            have hq_Bsub_idx : q.val ∣ Bsub.index := by
              simpa [hBsub_bot] using hq_H_card
            have hq_M_idx : q.val ∣ M.index := dvd_trans hq_Bsub_idx hBsub_index_dvd
            have hq_mem : q ∈ πM := hHallM.p_in_pi_of_p_dvd_card q hq_M_card
            have hq_not_mem : q ∉ πM := hHallM.p_in_pi_of_p_dvd_index q hq_M_idx
            exact hq_not_mem hq_mem
          have hBsub_card_gt : 1 < Nat.card Bsub :=
            (Subgroup.one_lt_card_iff_ne_bot (H := Bsub)).2 hBsub_ne_bot
          have hHstar_pos : 0 < Nat.card Hstar := Nat.card_pos
          have hHstar_lt_mul : Nat.card Hstar < Nat.card Bsub * Nat.card Hstar := by
            simpa [one_mul] using lt_mul_of_one_lt_left hHstar_pos hBsub_card_gt
          calc
            Nat.card HstarG = Nat.card Hstar := hHstarG_card
            _ < Nat.card Bsub * Nat.card Hstar := hHstar_lt_mul
            _ = Nat.card H := hcompB.card_mul
        have hmeasure_Hstar :
            Nat.card G + Nat.card HstarG < Nat.card G + Nat.card H := by
          exact Nat.add_lt_add_left hHstarG_lt _
        have hM_hall' : ∃ π₀, IsHallSubgroup π₀ M := ⟨πM, hHallM⟩
        have hM_quot_nil : QuotientByFittingIsNilpotent (G ⧸ M) := by
          by_cases hG₀bot : G₀ = ⊥
          · subst G₀
            have hM_eq : M = ⊤ := by simp [M]
            let eTop : (G ⧸ M) ≃* (G ⧸ (⊤ : Subgroup G)) :=
              QuotientGroup.quotientMulEquivOfEq hM_eq
            have htop_nil : QuotientByFittingIsNilpotent (G ⧸ (⊤ : Subgroup G)) := by
              letI : Subsingleton (G ⧸ (⊤ : Subgroup G)) :=
                QuotientGroup.subsingleton_quotient_top
              rw [QuotientByFittingIsNilpotent]
              infer_instance
            exact quotientByFittingIsNilpotent_of_mulEquiv eTop.symm htop_nil
          · have hM_eq : M = G₀ := by simp [M, hG₀bot]
            let eEq : (G ⧸ M) ≃* (G ⧸ G₀) :=
              QuotientGroup.quotientMulEquivOfEq hM_eq
            exact quotientByFittingIsNilpotent_of_mulEquiv eEq.symm hnil2
        have hIH_Hstar : theorem_6_4_goal π HstarG J₁ J₂ := by
          exact
            hind hHstar_pi' hM_hall' hM_nil hM_quot_nil
              hJ₁π hJ₂π hHstar_norm₁ hHstar_norm₂ hmeasure_Hstar
        obtain ⟨y, hyL, hyPi, hyCentHstar⟩ := hIH_Hstar
        have hB_cent_L : B ≤ Subgroup.centralizer (L : Set G) := by
          have hF_pi' : IsPiSubgroup (G := M) {p | p ∉ π} (fittingSubgroup M) := by
            intro p hp
            let FMG : Subgroup G := (fittingSubgroup M).map M.subtype
            have hFMG_card :
                Nat.card FMG = Nat.card (fittingSubgroup M) := by
              dsimp [FMG]
              simpa using
                (Subgroup.card_map_of_injective (K := fittingSubgroup M) (f := M.subtype)
                  (hf := Subtype.coe_injective))
            have hFMG_nil : Group.IsNilpotent FMG := by
              dsimp [FMG]
              let e :
                  fittingSubgroup M ≃* (fittingSubgroup M).map M.subtype :=
                Subgroup.equivMapOfInjective (f := M.subtype) (fittingSubgroup M)
                  M.subtype_injective
              exact
                nilpotent_of_mulEquiv (G := fittingSubgroup M)
                  (G' := (fittingSubgroup M).map M.subtype) e
            have hFMG_le_fitG : FMG ≤ fittingSubgroup G := by
              exact
                le_sSup ⟨
                  (inferInstance : FMG.Normal),
                  hFMG_nil
                ⟩
            have hp_FMG : p.val ∣ Nat.card FMG := by
              simpa [hFMG_card] using hp
            have hp_fitG : p.val ∣ Nat.card (fittingSubgroup G) := by
              exact dvd_trans hp_FMG (Subgroup.card_dvd_of_le hFMG_le_fitG)
            have hp_H : p.val ∣ Nat.card H := hcase2 p hp_fitG
            exact
              (IsPiGroup_iff {p | p ∉ π} H).1
                (IsPiSubgroup.isPiGroup (H := H) hHπ') p hp_H
          have hcommutator_map_eq_bot_core :
              ∀ {J C : Subgroup G}, IsPiSubgroup π J → B ≤ Subgroup.normalizer J → C = ⁅J, B⁆ →
                C ≤ M → IsPiSubgroup π C →
                (C.subgroupOf M).map (QuotientGroup.mk' (fittingSubgroup M)) = ⊥ := by
            intro J C hJ_pi hB_norm_J hC_eq hC_le_M hC_pi
            let qM : M →* M ⧸ fittingSubgroup M := QuotientGroup.mk' (fittingSubgroup M)
            let Bbar : Subgroup (M ⧸ fittingSubgroup M) := (B.subgroupOf M).map qM
            let Cbar : Subgroup (M ⧸ fittingSubgroup M) := (C.subgroupOf M).map qM
            have hQ_nil : Group.IsNilpotent (M ⧸ fittingSubgroup M) := hM_nil
            have hBbar_pi' : IsPiSubgroup {p | p ∉ π} Bbar := by
              intro p hp
              have hpBsub : p.val ∣ Nat.card (B.subgroupOf M) := by
                exact dvd_trans hp (Subgroup.card_map_dvd (H := B.subgroupOf M) qM)
              have hpB : p.val ∣ Nat.card B := by
                simpa [natCard_subgroupOf_eq B M hB_le_M] using hpBsub
              exact hB_pi' p hpB
            have hBbar_coprime_of_mem_pi {p : Nat.Primes} (hp_pi : p ∈ π) :
                Nat.Coprime p.val (Nat.card Bbar) := by
              refine (p.property.coprime_iff_not_dvd).2 ?_
              intro hpBbar
              have hp_pi' : p ∈ {p | p ∉ π} := hBbar_pi' p hpBbar
              exact hp_pi' hp_pi
            have hCbar_pi : IsPiGroup π Cbar := by
              rw [IsPiGroup_iff]
              intro p hp
              have hpCsub : p.val ∣ Nat.card (C.subgroupOf M) := by
                exact dvd_trans hp (Subgroup.card_map_dvd (H := C.subgroupOf M) qM)
              have hpC : p.val ∣ Nat.card C := by
                simpa [natCard_subgroupOf_eq C M hC_le_M] using hpCsub
              exact hC_pi p hpC
            have hCbar_pi' : IsPiGroup {p | p ∉ π} Cbar := by
              rw [IsPiGroup_iff]
              intro p hp
              have hp_pi : p ∈ π := (IsPiGroup_iff π Cbar).1 hCbar_pi p hp
              letI : Fact p.val.Prime := ⟨p.property⟩
              let P : Subgroup (M ⧸ fittingSubgroup M) := pPrimeCore p.val (M ⧸ fittingSubgroup M)
              have hquot_core_bot : pPrimeCore p.val ((M ⧸ fittingSubgroup M) ⧸ P) = ⊥ := by
                simpa [P] using
                  (pPrimeCore_quotient_pPrimeCore_eq_bot (G := M ⧸ fittingSubgroup M) (p := p.val))
              have hquot_nil : Group.IsNilpotent ((M ⧸ fittingSubgroup M) ⧸ P) := by
                letI : Group.IsNilpotent (M ⧸ fittingSubgroup M) := hQ_nil
                infer_instance
              have hquot_top_nil : Group.IsNilpotent (↥(⊤ : Subgroup ((M ⧸ fittingSubgroup M) ⧸ P))) := by
                simpa using hquot_nil
              have hquot_top_p : IsPGroup p.val (⊤ : Subgroup ((M ⧸ fittingSubgroup M) ⧸ P)) := by
                exact
                  isPGroup_of_nilpotent_normal (G := (M ⧸ fittingSubgroup M) ⧸ P) (p := p.val)
                    (⊤ : Subgroup ((M ⧸ fittingSubgroup M) ⧸ P)) inferInstance hquot_top_nil
                    hquot_core_bot
              have hpcore_top : pCore p.val ((M ⧸ fittingSubgroup M) ⧸ P) = ⊤ := by
                apply top_unique
                exact le_sSup ⟨
                  (inferInstance : (⊤ : Subgroup ((M ⧸ fittingSubgroup M) ⧸ P)).Normal),
                  hquot_top_p
                ⟩
              have hOp_top : Op_p'p p.val (M ⧸ fittingSubgroup M) = ⊤ := by
                simp [Op_p'p, P, hpcore_top]
              have hBbar_coprime : Nat.Coprime p.val (Nat.card Bbar) :=
                hBbar_coprime_of_mem_pi hp_pi
              have hBbar_le_P : Bbar ≤ P := by
                have hBbar_le_Op : Bbar ≤ Op_p'p p.val (M ⧸ fittingSubgroup M) := by
                  simp [hOp_top]
                exact
                  le_pPrimeCore_of_le_Op_p'p_of_coprime
                    (G := M ⧸ fittingSubgroup M) (p := p.val) hBbar_le_Op hBbar_coprime
              let Nsub : Subgroup M := P.comap qM
              have hNsub_char : Nsub.Characteristic := by
                letI : P.Characteristic := by
                  dsimp [P]
                  infer_instance
                dsimp [Nsub, qM]
                exact
                  Subgroup.Characteristic.comap_quotient_mk
                    (H := fittingSubgroup M) (K := P) (hK := inferInstance)
              let N : Subgroup G := Nsub.map M.subtype
              have hBsub_le_Nsub : B.subgroupOf M ≤ Nsub := by
                intro x hx
                show qM x ∈ P
                exact hBbar_le_P (Subgroup.mem_map_of_mem qM hx)
              have hN_normal : N.Normal := by
                letI : Nsub.Characteristic := hNsub_char
                dsimp [N]
                infer_instance
              letI : N.Normal := hN_normal
              have hB_le_N : B ≤ N := by
                intro x hx
                refine Subgroup.mem_map.mpr ?_
                refine ⟨⟨x, hB_le_M hx⟩, ?_, rfl⟩
                exact hBsub_le_Nsub (by simpa [Subgroup.mem_subgroupOf] using hx)
              let qN : G →* G ⧸ N := QuotientGroup.mk' N
              have hBmap_bot : B.map qN = ⊥ := by
                have hB_le_ker : B ≤ qN.ker := by
                  simpa [qN, QuotientGroup.ker_mk'] using hB_le_N
                exact (Subgroup.map_eq_bot_iff (H := B) (f := qN)).2 hB_le_ker
              have hC_le_N : C ≤ N := by
                have hCmap_bot : C.map qN = ⊥ := by
                  calc
                    C.map qN = ⁅J.map qN, B.map qN⁆ := by
                      rw [hC_eq, Subgroup.map_commutator]
                    _ = ⊥ := by
                      rw [hBmap_bot, Subgroup.commutator_bot_right]
                have hC_le_ker : C ≤ qN.ker :=
                  (Subgroup.map_eq_bot_iff (H := C) (f := qN)).mp hCmap_bot
                simpa [qN, QuotientGroup.ker_mk'] using hC_le_ker
              have hCsub_le_Nsub : C.subgroupOf M ≤ Nsub := by
                intro x hx
                have hxC : ((x : M) : G) ∈ C := by
                  simpa [Subgroup.mem_subgroupOf] using hx
                have hxN : ((x : M) : G) ∈ N := hC_le_N hxC
                rcases Subgroup.mem_map.mp hxN with ⟨y, hy, hyx⟩
                have hy_eq : y = x := by
                  apply M.subtype_injective
                  exact hyx
                simpa [hy_eq] using hy
              have hCbar_le_P : Cbar ≤ P := by
                intro x hx
                rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
                exact hCsub_le_Nsub hy
              have hCbar_coprime : Nat.Coprime p.val (Nat.card Cbar) := by
                exact Nat.Coprime.of_dvd_right
                  (Subgroup.card_dvd_of_le hCbar_le_P)
                  (pPrimeCore_coprime_card (G := M ⧸ fittingSubgroup M) (p := p.val))
              exact False.elim (((p.property.coprime_iff_not_dvd).1 hCbar_coprime) hp)
            have hCbar_card_one : Nat.card Cbar = 1 := by
              exact (Nat.coprime_self _).1
                (coprime_card_of_isPiGroup_compl (G := Cbar) (A := Cbar) hCbar_pi hCbar_pi')
            exact (Subgroup.card_eq_one (H := Cbar)).1 hCbar_card_one
          have hB_cent_J₁ : B ≤ Subgroup.centralizer (J₁ : Set G) := by
            let JB : Subgroup G := B ⊔ J₁
            let C : Subgroup G := ⁅J₁, B⁆
            have hB_norm_J₁ : B ≤ Subgroup.normalizer J₁ := le_trans hB_le_H hnorm₁
            have hC_le_J₁ : C ≤ J₁ := by
              haveI : (J₁.subgroupOf JB).Normal := by
                simpa [JB] using
                  (Subgroup.normal_subgroupOf_sup_of_le_normalizer (H := B) (N := J₁) hB_norm_J₁)
              have hcomm_le :
                  ⁅J₁.subgroupOf JB, B.subgroupOf JB⁆ ≤ J₁.subgroupOf JB :=
                Subgroup.commutator_le_left (H₁ := J₁.subgroupOf JB) (H₂ := B.subgroupOf JB)
              have hJ₁sub_map : (J₁.subgroupOf JB).map JB.subtype = J₁ := by
                ext x
                constructor
                · rintro ⟨y, hy, rfl⟩
                  exact hy
                · intro hx
                  exact Subgroup.mem_map.mpr ⟨⟨x, (show J₁ ≤ JB from le_sup_right) hx⟩, hx, rfl⟩
              have hBsub_map : (B.subgroupOf JB).map JB.subtype = B := by
                ext x
                constructor
                · rintro ⟨y, hy, rfl⟩
                  exact hy
                · intro hx
                  exact Subgroup.mem_map.mpr ⟨⟨x, (show B ≤ JB from le_sup_left) hx⟩, hx, rfl⟩
              have hcomm_map :
                  (⁅J₁.subgroupOf JB, B.subgroupOf JB⁆).map JB.subtype = C := by
                calc
                  (⁅J₁.subgroupOf JB, B.subgroupOf JB⁆).map JB.subtype
                      = ⁅(J₁.subgroupOf JB).map JB.subtype, (B.subgroupOf JB).map JB.subtype⁆ := by
                          rw [Subgroup.map_commutator]
                  _ = C := by
                    rw [hJ₁sub_map, hBsub_map]
              have hmap_le :
                  (⁅J₁.subgroupOf JB, B.subgroupOf JB⁆).map JB.subtype ≤
                    (J₁.subgroupOf JB).map JB.subtype :=
                Subgroup.map_mono hcomm_le
              calc
                C = (⁅J₁.subgroupOf JB, B.subgroupOf JB⁆).map JB.subtype := by
                  rw [hcomm_map]
                _ ≤ (J₁.subgroupOf JB).map JB.subtype := hmap_le
                _ = J₁ := hJ₁sub_map
            have hC_le_M : C ≤ M := by
              calc
                C = ⁅J₁, B⁆ := rfl
                _ ≤ ⁅J₁, M⁆ := Subgroup.commutator_mono le_rfl hB_le_M
                _ ≤ M := Subgroup.commutator_le_right (H₁ := J₁) (H₂ := M)
            have hC_pi : IsPiSubgroup π C := by
              intro p hp
              exact hJ₁π p (dvd_trans hp (Subgroup.card_dvd_of_le hC_le_J₁))
            have hC_eq_bot : C = ⊥ := by
              let qM : M →* M ⧸ fittingSubgroup M := QuotientGroup.mk' (fittingSubgroup M)
              have hCmap_eq_bot : (C.subgroupOf M).map qM = ⊥ := by
                simpa [qM] using
                  hcommutator_map_eq_bot_core (J := J₁) (C := C) hJ₁π hB_norm_J₁ rfl hC_le_M hC_pi
              have hC_le_F : C.subgroupOf M ≤ fittingSubgroup M := by
                simpa [qM, QuotientGroup.ker_mk'] using
                  (Subgroup.map_eq_bot_iff (H := C.subgroupOf M) (f := qM)).mp hCmap_eq_bot
              have hcop_C_F : Nat.Coprime (Nat.card C) (Nat.card (fittingSubgroup M)) := by
                apply Nat.coprime_of_dvd'
                intro k hk hkC hkF
                let q : Nat.Primes := ⟨k, hk⟩
                have hq_pi : q ∈ π := hC_pi q (by simpa [q] using hkC)
                have hq_pi' : q ∈ {p | p ∉ π} := hF_pi' q (by simpa [q] using hkF)
                exact False.elim (hq_pi' hq_pi)
              have hcard_C_dvd_F : Nat.card C ∣ Nat.card (fittingSubgroup M) := by
                have hcard_sub_dvd : Nat.card (C.subgroupOf M) ∣ Nat.card (fittingSubgroup M) :=
                  Subgroup.card_dvd_of_le hC_le_F
                simpa [natCard_subgroupOf_eq C M hC_le_M] using hcard_sub_dvd
              have hcard_C_eq_one : Nat.card C = 1 := by
                exact Nat.eq_one_of_dvd_coprimes hcop_C_F dvd_rfl hcard_C_dvd_F
              exact (Subgroup.card_eq_one (H := C)).mp hcard_C_eq_one
            exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := J₁) (H₂ := B)).mp hC_eq_bot |>
              (Subgroup.le_centralizer_iff (H := J₁) (K := B)).mp
          have hB_cent_J₂ : B ≤ Subgroup.centralizer (J₂ : Set G) := by
            let JB : Subgroup G := B ⊔ J₂
            let C : Subgroup G := ⁅J₂, B⁆
            have hB_norm_J₂ : B ≤ Subgroup.normalizer J₂ := le_trans hB_le_H hnorm₂
            have hC_le_J₂ : C ≤ J₂ := by
              haveI : (J₂.subgroupOf JB).Normal := by
                simpa [JB] using
                  (Subgroup.normal_subgroupOf_sup_of_le_normalizer (H := B) (N := J₂) hB_norm_J₂)
              have hcomm_le :
                  ⁅J₂.subgroupOf JB, B.subgroupOf JB⁆ ≤ J₂.subgroupOf JB :=
                Subgroup.commutator_le_left (H₁ := J₂.subgroupOf JB) (H₂ := B.subgroupOf JB)
              have hJ₂sub_map : (J₂.subgroupOf JB).map JB.subtype = J₂ := by
                ext x
                constructor
                · rintro ⟨y, hy, rfl⟩
                  exact hy
                · intro hx
                  exact Subgroup.mem_map.mpr ⟨⟨x, (show J₂ ≤ JB from le_sup_right) hx⟩, hx, rfl⟩
              have hBsub_map : (B.subgroupOf JB).map JB.subtype = B := by
                ext x
                constructor
                · rintro ⟨y, hy, rfl⟩
                  exact hy
                · intro hx
                  exact Subgroup.mem_map.mpr ⟨⟨x, (show B ≤ JB from le_sup_left) hx⟩, hx, rfl⟩
              have hcomm_map :
                  (⁅J₂.subgroupOf JB, B.subgroupOf JB⁆).map JB.subtype = C := by
                calc
                  (⁅J₂.subgroupOf JB, B.subgroupOf JB⁆).map JB.subtype
                      = ⁅(J₂.subgroupOf JB).map JB.subtype, (B.subgroupOf JB).map JB.subtype⁆ := by
                          rw [Subgroup.map_commutator]
                  _ = C := by
                    rw [hJ₂sub_map, hBsub_map]
              have hmap_le :
                  (⁅J₂.subgroupOf JB, B.subgroupOf JB⁆).map JB.subtype ≤
                    (J₂.subgroupOf JB).map JB.subtype :=
                Subgroup.map_mono hcomm_le
              calc
                C = (⁅J₂.subgroupOf JB, B.subgroupOf JB⁆).map JB.subtype := by
                  rw [hcomm_map]
                _ ≤ (J₂.subgroupOf JB).map JB.subtype := hmap_le
                _ = J₂ := hJ₂sub_map
            have hC_le_M : C ≤ M := by
              calc
                C = ⁅J₂, B⁆ := rfl
                _ ≤ ⁅J₂, M⁆ := Subgroup.commutator_mono le_rfl hB_le_M
                _ ≤ M := Subgroup.commutator_le_right (H₁ := J₂) (H₂ := M)
            have hC_pi : IsPiSubgroup π C := by
              intro p hp
              exact hJ₂π p (dvd_trans hp (Subgroup.card_dvd_of_le hC_le_J₂))
            have hC_eq_bot : C = ⊥ := by
              let qM : M →* M ⧸ fittingSubgroup M := QuotientGroup.mk' (fittingSubgroup M)
              have hCmap_eq_bot : (C.subgroupOf M).map qM = ⊥ := by
                simpa [qM] using
                  hcommutator_map_eq_bot_core (J := J₂) (C := C) hJ₂π hB_norm_J₂ rfl hC_le_M hC_pi
              have hC_le_F : C.subgroupOf M ≤ fittingSubgroup M := by
                simpa [qM, QuotientGroup.ker_mk'] using
                  (Subgroup.map_eq_bot_iff (H := C.subgroupOf M) (f := qM)).mp hCmap_eq_bot
              have hcop_C_F : Nat.Coprime (Nat.card C) (Nat.card (fittingSubgroup M)) := by
                apply Nat.coprime_of_dvd'
                intro k hk hkC hkF
                let q : Nat.Primes := ⟨k, hk⟩
                have hq_pi : q ∈ π := hC_pi q (by simpa [q] using hkC)
                have hq_pi' : q ∈ {p | p ∉ π} := hF_pi' q (by simpa [q] using hkF)
                exact False.elim (hq_pi' hq_pi)
              have hcard_C_dvd_F : Nat.card C ∣ Nat.card (fittingSubgroup M) := by
                have hcard_sub_dvd : Nat.card (C.subgroupOf M) ∣ Nat.card (fittingSubgroup M) :=
                  Subgroup.card_dvd_of_le hC_le_F
                simpa [natCard_subgroupOf_eq C M hC_le_M] using hcard_sub_dvd
              have hcard_C_eq_one : Nat.card C = 1 := by
                exact Nat.eq_one_of_dvd_coprimes hcop_C_F dvd_rfl hcard_C_dvd_F
              exact (Subgroup.card_eq_one (H := C)).mp hcard_C_eq_one
            exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := J₂) (H₂ := B)).mp hC_eq_bot |>
              (Subgroup.le_centralizer_iff (H := J₂) (K := B)).mp
          have hJ₁_cent_B : J₁ ≤ Subgroup.centralizer (B : Set G) :=
            (Subgroup.le_centralizer_iff (H := B) (K := J₁)).mp hB_cent_J₁
          have hJ₂_cent_B : J₂ ≤ Subgroup.centralizer (B : Set G) :=
            (Subgroup.le_centralizer_iff (H := B) (K := J₂)).mp hB_cent_J₂
          have hL_cent_B : L ≤ Subgroup.centralizer (B : Set G) := by
            exact sup_le hJ₁_cent_B hJ₂_cent_B
          exact (Subgroup.le_centralizer_iff (H := B) (K := L)).mpr hL_cent_B
        have hyCentB : y ∈ Subgroup.centralizer (B : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro b hbB
          exact ((Subgroup.mem_centralizer_iff.mp (hB_cent_L hbB)) y hyL).symm
        have hHstarG_mem : ∀ u : Hstar, ((u : H) : G) ∈ HstarG := by
          intro u
          exact Subgroup.mem_map.mpr ⟨u, u.property, rfl⟩
        have hB_mem : ∀ b : Bsub, (((b : Bsub) : H) : G) ∈ B := by
          intro b
          rw [← hBsub_map]
          exact Subgroup.mem_map.mpr ⟨b, b.property, rfl⟩
        have hdecomp_H :
            ∀ z : H, ∃ b : Bsub, ∃ u : Hstar, ((z : H) : G) = (((b : Bsub) : H) : G) * (((u : Hstar) : H) : G) := by
          intro z
          have hzsup : z ∈ Bsub ⊔ Hstar := by
            simp [hcompB.sup_eq_top]
          rcases (Subgroup.mem_sup_of_normal_left (s := Bsub) (t := Hstar) (x := z)).1 hzsup with
            ⟨b, hbB, u, huHstar, hbu⟩
          exact ⟨⟨b, hbB⟩, ⟨u, huHstar⟩, congrArg Subtype.val hbu.symm⟩
        have hyCentH : y ∈ Subgroup.centralizer (H : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro h hhH
          let hH : H := ⟨h, hhH⟩
          rcases hdecomp_H hH with ⟨b, u, h_eq⟩
          have huHstarG : (((u : Hstar) : H) : G) ∈ HstarG := hHstarG_mem u
          have hbBG : (((b : Bsub) : H) : G) ∈ B := hB_mem b
          have hyu :
              y * (((u : Hstar) : H) : G) = (((u : Hstar) : H) : G) * y := by
            exact (Subgroup.mem_centralizer_iff.mp hyCentHstar _ huHstarG).symm
          have hyb :
              (((b : Bsub) : H) : G) * y = y * (((b : Bsub) : H) : G) := by
            exact Subgroup.mem_centralizer_iff.mp hyCentB _ hbBG
          calc
            h * y = ((((b : Bsub) : H) : G) * (((u : Hstar) : H) : G)) * y := by
              rw [show h = (((b : Bsub) : H) : G) * (((u : Hstar) : H) : G) by
                simpa using h_eq]
            _ = (((b : Bsub) : H) : G) * ((((u : Hstar) : H) : G) * y) := by
              simp [mul_assoc]
            _ = (((b : Bsub) : H) : G) * (y * (((u : Hstar) : H) : G)) := by
              rw [hyu.symm]
            _ = ((((b : Bsub) : H) : G) * y) * (((u : Hstar) : H) : G) := by
              simp [mul_assoc]
            _ = (y * (((b : Bsub) : H) : G)) * (((u : Hstar) : H) : G) := by
              rw [hyb]
            _ = y * ((((b : Bsub) : H) : G) * (((u : Hstar) : H) : G)) := by
              simp [mul_assoc]
            _ = y * h := by
              rw [show h = (((b : Bsub) : H) : G) * (((u : Hstar) : H) : G) by
                simpa using h_eq]
        exact ⟨y, hyL, hyPi, hyCentH⟩
      by_cases hcase1 : ∃ p : Nat.Primes, p.val ∣ Nat.card (fittingSubgroup G) ∧ ¬ p.val ∣ Nat.card H
      · exact hcase1_main hcase1
      · refine hcase2_main ?_
        intro p hp
        by_contra hpH
        exact hcase1 ⟨p, hp, hpH⟩
    by_cases hLH : L ⊔ H = ⊤
    · obtain ⟨x, hxL, hxpi, hxcent⟩ := hcase_eq_LH hLH
      exact ⟨x, hxL, hxpi, hxcent⟩
    · have hproper : L ⊔ H < ⊤ := lt_of_le_of_ne le_top hLH
      obtain ⟨x, hxL, hxpi, hxcent⟩ := hreduce_LH hproper
      exact ⟨x, hxL, hxpi, hxcent⟩
  · haveI : Subsingleton G := not_nontrivial_iff_subsingleton.mp hGnontriv
    have hbot_pi : IsPiSubgroup (G := G) π (⊥ : Subgroup G) := by
      intro p hp
      exfalso
      have : p.val ∣ (1 : ℕ) := by
        simpa using hp
      exact p.property.not_dvd_one this
    have hJ₁bot : J₁ = ⊥ := Subgroup.eq_bot_of_subsingleton (H := J₁)
    have hJ₂bot : J₂ = ⊥ := Subgroup.eq_bot_of_subsingleton (H := J₂)
    refine ⟨1, ?_, ?_, ?_⟩
    · simp [hJ₁bot, hJ₂bot]
    · simpa [hJ₁bot, hJ₂bot, Subgroup.conjBy] using hbot_pi
    · simp

public theorem theorem_6_4
    {G : Type u64} [Group G] [Finite G] {π : Set Nat.Primes}
    {H : Subgroup G} (hHπ' : IsPiSubgroup {p | p ∉ π} H)
    {G₀ : Subgroup G} [G₀.Normal] (hG₀Hall : ∃ π₀ : Set Nat.Primes, IsHallSubgroup π₀ G₀)
    (hnil1 : QuotientByFittingIsNilpotent G₀) (hnil2 : QuotientByFittingIsNilpotent (G ⧸ G₀))
    {J₁ J₂ : Subgroup G} (hJ₁π : IsPiSubgroup π J₁) (hJ₂π : IsPiSubgroup π J₂)
    (hnorm₁ : H ≤ Subgroup.normalizer J₁) (hnorm₂ : H ≤ Subgroup.normalizer J₂) :
    theorem_6_4_goal π H J₁ J₂ := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ {G' : Type u64} [Group G'] [Finite G'] {π' : Set Nat.Primes}
      {H' : Subgroup G'}, IsPiSubgroup {p | p ∉ π'} H' →
      ∀ {G₀' : Subgroup G'} [G₀'.Normal],
      (∃ π₀ : Set Nat.Primes, IsHallSubgroup π₀ G₀') →
      QuotientByFittingIsNilpotent G₀' →
      QuotientByFittingIsNilpotent (G' ⧸ G₀') →
      ∀ {J₁' J₂' : Subgroup G'},
      IsPiSubgroup π' J₁' →
      IsPiSubgroup π' J₂' →
      H' ≤ Subgroup.normalizer J₁' →
      H' ≤ Subgroup.normalizer J₂' →
      Nat.card G' + Nat.card H' = n →
      theorem_6_4_goal π' H' J₁' J₂'
  have hP : ∀ n, P n := by
    intro n
    exact Nat.strong_induction_on (p := P) n <| fun n ih =>
      by
        intro G' _ _ π' H' hHπ' G₀' _ hG₀Hall hnil1 hnil2 J₁' J₂' hJ₁π hJ₂π hnorm₁ hnorm₂ hmeasure
        refine theorem_6_4_main
          (G := G') (π := π') (H := H') hHπ'
          (G₀ := G₀') hG₀Hall hnil1 hnil2
          (J₁ := J₁') (J₂ := J₂') hJ₁π hJ₂π hnorm₁ hnorm₂ ?_
        intro G'' _ _ π'' H'' hHπ'' G₀'' _ hG₀Hall'' hnil1'' hnil2'' J₁'' J₂'' hJ₁π'' hJ₂π'' hnorm₁'' hnorm₂'' hlt
        have hlt' : Nat.card G'' + Nat.card H'' < n := by
          simpa [hmeasure] using hlt
        exact
          ih _ hlt'
            (G' := G'') (π' := π'') (H' := H'') hHπ''
            (G₀' := G₀'') hG₀Hall'' hnil1'' hnil2''
            (J₁' := J₁'') (J₂' := J₂'') hJ₁π'' hJ₂π'' hnorm₁'' hnorm₂'' rfl
  exact
    hP (Nat.card G + Nat.card H)
      (G' := G) (π' := π) (H' := H) hHπ'
      (G₀' := G₀) hG₀Hall hnil1 hnil2
      (J₁' := J₁) (J₂' := J₂) hJ₁π hJ₂π hnorm₁ hnorm₂ rfl
