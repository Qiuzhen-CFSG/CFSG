module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.ModelSeparation
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.MaximalLevi
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
/-!
# Exceptional sections exclude the binary four- and five-space containing models

In dimension four, the exceptional section order forces the smaller group
to be the whole containing group; the actual carrier separation then rules
out its exceptional two-core quotient.

In dimension five, a proper full-Sylow overgroup is an actual partial-flag
stabilizer, hence lies in a maximal subspace parabolic. The perfect smaller
group retains its original exceptional section through that parabolic's
two-core quotient. The quotient is PSL₄(2), already excluded, or
S₃ × PSL₃(2), whose order is too small. If the full-Sylow join is the whole
group, the supplied Sylow normalization makes the smaller group normal;
simplicity and the original exceptional orders give the contradiction.

Source: Aschbacher–Smith A.3.12, pp.47–48, applied to 13.6.27, p.934;
the actual binary five-space parabolic quotients also occur in 15.3.24.
-/
public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
private theorem model_of_top_section [IsSimpleGroup G] (B : Subgroup G)
    (hsection : IsModel (B ⧸ pCore 2 B)) (hB : B = ⊤) : IsModel G := by
  let eB : B ≃* G := (MulEquiv.subgroupCongr hB).trans topEquiv
  let : IsSimpleGroup B := eB.isSimpleGroup
  have hcore : pCore 2 B = ⊥ := by
    rcases (inferInstance : (pCore 2 B).Normal).eq_bot_or_eq_top with hc | hc
    · exact hc
    · have hd := hsection.card_dvd
      rw [hc] at hd
      simp at hd
  let q : B ≃* B ⧸ pCore 2 B := QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hcore.symm)
  exact hsection.of_equiv (eB.symm.trans q)

private noncomputable def binaryProjectiveEquiv {n : ℕ}
    (hm : ClassicalGroup.IsPSL G n 2) : G ≃* PSL(n,ZMod 2) :=
  Classical.choice <| by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let := Fintype.ofFinite F
    let k : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
      simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
    exact ⟨e.trans (Atlas.fieldEquivPSL n k)⟩

private theorem binary_card (n : ℕ) [NeZero n] :
    Nat.card PSL(n,ZMod 2) = ∏ i : Fin n, (2^n-2^i.val) := by
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) n
  simpa only [Nat.card_zmod, show 2-1=1 from rfl, Nat.gcd_one_right,mul_one] using h

/-- An exceptional two-core section cannot occur in any subgroup of PSL₄(2). -/
theorem not_section_of_binaryFour (B : Subgroup G)
    (hsection : IsModel (B ⧸ pCore 2 B))
    (hm : ClassicalGroup.IsPSL G 4 2) : False := by
  let e := binaryProjectiveEquiv hm
  let : IsSimpleGroup PSL(4,ZMod 2) := Atlas.psl_simple_high_rank 4 (by decide)
  let : IsSimpleGroup G := e.isSimpleGroup
  have hc : Nat.card G = 20160 := by
    rw [Nat.card_congr e.toEquiv]
    rw [binary_card]
    decide
  exact (model_of_top_section B hsection (eq_top_of_card_le B hsection hc.le)).not_binaryFour hm

open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.FiveFlagGeometry.MaximalOvergroups
private instance : Finite (LinearGroup 5) :=
  Finite.of_injective (fun g : LinearGroup 5 => (g : Space 5 → Space 5)) DFunLike.coe_injective
private theorem no_section_maximal_parabolic (B : Subgroup (LinearGroup 5))
    [Group.IsPerfect B] (hsection : IsModel (B ⧸ pCore 2 B))
    (b : FiveBasis) (i : Fin 4) (hBP : B ≤ flagStabilizer b {i}) : False := by
  let P := flagStabilizer b {i}
  let D := B.subgroupOf P
  let eD : D ≃* B := subgroupOfEquivOfLe hBP
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective (f := eD.symm.toMonoidHom) eD.symm.surjective
  have hD : IsModel (D ⧸ pCore 2 D) := hsection.of_equiv
    (QuotientGroup.congr _ _ eD (pCore_map_iso 2 eD))
  let q := QuotientGroup.mk' (pCore 2 P)
  let : Group.IsNilpotent (pCore 2 P) := pCore_isNilpotent
  let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
  have himage := section_map D hD q
  rcases singleton_quotient_models b i with hsmall | hfour
  · obtain ⟨e⟩ := hsmall
    have hd := ambient_card_dvd himage
    rw [Nat.card_congr e.toEquiv,Nat.card_prod,Nat.card_perm,Nat.card_fin] at hd
    rw [binary_card] at hd
    exact (by decide : ¬ 20160 ∣ Nat.factorial 3 * (∏ i : Fin 3, (2^3-2^i.val))) hd
  · obtain ⟨e⟩ := hfour
    exact not_section_of_binaryFour (D.map q) himage
      ⟨ZMod 2,inferInstance,inferInstance,Nat.card_zmod 2,⟨e⟩⟩

private theorem not_section_linearFive (S : Sylow 2 (LinearGroup 5))
    (B : Subgroup (LinearGroup 5)) (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup (LinearGroup 5)) ≤ normalizer (B : Set (LinearGroup 5)))
    (hsection : IsModel (B ⧸ pCore 2 B)) : False := by
  let e := projectiveEquivLinear (by decide : 0 < 5)
  let : IsSimpleGroup PSL(5,ZMod 2) := Atlas.psl_simple_high_rank 5 (by decide)
  let : IsSimpleGroup (LinearGroup 5) := e.symm.isSimpleGroup
  let : Group.IsPerfect B := local_perfect hB
  by_cases htop : B ⊔ (S : Subgroup (LinearGroup 5)) = ⊤
  · have hnB : B.Normal := normalizer_eq_top_iff.mp
      (top_unique (htop ▸ sup_le le_normalizer hn))
    have hBt : B = ⊤ := by
      rcases hnB.eq_bot_or_eq_top with hb | hb
      · exact (hB.ne_bot (by simp [hb])).elim
      · exact hb
    have hm := model_of_top_section B hsection hBt
    have hc : Nat.card (LinearGroup 5) = 9999360 := by
      rw [← Nat.card_congr e.toEquiv]
      rw [binary_card]
      decide
    rcases hm.card with hh | hh | hh <;> omega
  · obtain ⟨b,cuts,hcuts⟩ := isFlagParabolic_of_sylow_le S
      (B ⊔ (S : Subgroup (LinearGroup 5))) le_sup_right
    have hnonempty : cuts.Nonempty := by
      by_contra hh
      have he : cuts = ∅ := Set.not_nonempty_iff_eq_empty.mp hh
      exact htop (hcuts.trans (he ▸ flagStabilizer_empty b))
    obtain ⟨i,hi⟩ := hnonempty
    exact no_section_maximal_parabolic B hsection b i
      (le_sup_left.trans (hcuts.le.trans ((flag_le_iff b _ _).mpr
        (Set.singleton_subset_iff.mpr hi))))

/-- The original Sylow-normalized exceptional local component excludes PSL₅(2). -/
theorem not_section_of_binaryFive (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S) (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hsection : IsModel (B ⧸ pCore 2 B)) (hm : ClassicalGroup.IsPSL G 5 2) : False := by
  let e := (binaryProjectiveEquiv hm).trans (projectiveEquivLinear (by decide : 0 < 5))
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]
    infer_instance
  obtain ⟨hl,hn',hs⟩ := local_section_map hB hn hsection e.toMonoidHom
  exact not_section_linearFive (S.mapSurjective e.surjective) (B.map e.toMonoidHom) hl hn' hs

/-- Both binary higher-linear containing rows are excluded without a smaller-group quasisimplicity premise. -/
theorem not_section_of_binaryFour_or_Five (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S) (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hsection : IsModel (B ⧸ pCore 2 B)) {d : ℕ} (hd : d=4 ∨ d=5)
    (hm : ClassicalGroup.IsPSL G d 2) : False := by
  rcases hd with rfl | rfl
  · exact not_section_of_binaryFour B hsection hm
  · exact not_section_of_binaryFive S B hB hn hsection hm
end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional
