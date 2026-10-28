module

public import Stellmacher.SectionOne.OneSevenFactorAction
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Defs
public import Theory.GroupAction.NormalizingActor

/-!
# Uniqueness of the small factors in Stellmacher (1.7)

Under the faithful elementary-abelian action of Section 1, two candidate
`SL₂(2)` factors with the same derived subgroup coincide. Their join normalizes
the common derived subgroup, preserves its four-element commutator space, and
fixes its coprime fixed-point complement pointwise. Faithfulness therefore
embeds the join into `GL₂(2)`, of order six; each given factor already has
order six.

This supplies the equal-derived-subgroup branch of the pairwise factor
argument in Stellmacher, Lemma (1.7), following
`refs/latex/stellmacher-n-group.tex`.
-/

open scoped IsMulCommutative

namespace Stellmacher.SectionOne

universe u

public theorem oneSevenFactor_eq_of_derived_eq
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (D E : Subgroup G)
    (hD : IsOneSevenFactor (V := V) D) (hE : IsOneSevenFactor (V := V) E)
    (hderived : (commutator D).map D.subtype = (commutator E).map E.subtype) :
    D = E := by
  let F : Subgroup G := (commutator D).map D.subtype
  let U : Subgroup V := commutatorAction F V
  let C : Subgroup V := FixedPoints.subgroup F V
  let K : Subgroup G := D ⊔ E
  have hFnormD : D ≤ Subgroup.normalizer (F : Set G) := by
    change D ≤ Subgroup.normalizer (((commutator D).map D.subtype : Subgroup G) : Set G)
    rw [Subgroup.map_subtype_commutator]
    exact Subgroup.normalizer_commutator_ge_left D D
  have hFnormE : E ≤ Subgroup.normalizer (F : Set G) := by
    change E ≤ Subgroup.normalizer (((commutator D).map D.subtype : Subgroup G) : Set G)
    rw [hderived, Subgroup.map_subtype_commutator]
    exact Subgroup.normalizer_commutator_ge_left E E
  have hFnormK : K ≤ Subgroup.normalizer (F : Set G) := sup_le hFnormD hFnormE
  let _ : IsInvariant K V U :=
    _root_.commutatorAction_isInvariant_of_normalizing_actor K F hFnormK
  let _ : IsElementaryAbelian 2 U := RankOneThreeGroupAssembly.isElementaryAbelian_subgroup U
  have hUcard : Nat.card U = 4 := hD.2.1.2.2
  have hKfix : K ≤ fixingSubgroup G (C : Set V) := by
    apply sup_le
    · intro d hd
      rw [mem_fixingSubgroup_iff]
      exact fun v hv => oneSevenFactor_fixes_derived_fixedPoints D hD d hd v hv
    · intro e he
      rw [mem_fixingSubgroup_iff]
      intro v hv
      apply oneSevenFactor_fixes_derived_fixedPoints E hE e he v
      change v ∈ FixedPoints.subgroup ((commutator D).map D.subtype) V at hv
      rw [hderived] at hv
      exact hv
  have hcop : Nat.Coprime (Nat.card F) (Nat.card V) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    have hFcard : Nat.card F = 3 := hD.2.1.2.1
    rw [hFcard, hn]
    exact (show Nat.Coprime 3 2 by decide).pow_right n
  have hcompl : IsCompl C U :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := F)
      (Group.isSolvable_of_comm (fun x y => IsMulCommutative.is_comm.comm x y))
      hcop inferInstance
  let ρ := Representation.ofElementaryAbelianAction (A := K) (G := U) (p := 2)
  have hρinj : Function.Injective ρ.asGroupHom := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm
    · intro k hk
      have hkρ : ρ k = 1 := congrArg Units.val (MonoidHom.mem_ker.mp hk)
      have hkU (u : U) : k • u = u := by
        apply Additive.ofMul.injective
        have heq := LinearMap.congr_fun hkρ (Additive.ofMul u)
        simpa only [ρ, Representation.ofElementaryAbelianAction_apply_ofMul,
          Module.End.one_apply] using heq
      have hkC (c : V) (hc : c ∈ C) : (k : G) • c = c :=
        (mem_fixingSubgroup_iff (M := G) (s := (C : Set V))).mp (hKfix k.property) c hc
      have hkV : (k : G) ∈ fixingSubgroup G (Set.univ : Set V) := by
        rw [mem_fixingSubgroup_iff]
        intro v _
        have hv : v ∈ C ⊔ U := by rw [hcompl.sup_eq_top]; exact Subgroup.mem_top v
        let _ : C.Normal := Subgroup.normal_of_isMulCommutative C
        obtain ⟨c, hc, u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hv
        have hku : (k : G) • u = u := congrArg Subtype.val (hkU ⟨u, hu⟩)
        rw [smul_mul', hkC c hc, hku]
      rw [h.action_faithful] at hkV
      apply Subtype.ext
      exact hkV
    · exact bot_le
  have hdim : Module.finrank (ZMod 2) (Additive U) = 2 := by
    have hc : Nat.card (Additive U) = 4 :=
      (Nat.card_congr Additive.toMul).trans hUcard
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)] at hc
    norm_num at hc
    exact Nat.pow_right_injective (by omega : 1 < 2) hc
  let b : Module.Basis (Fin 2) (ZMod 2) (Additive U) :=
    Module.finBasisOfFinrankEq (ZMod 2) (Additive U) hdim
  let φ : K →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) :=
    (Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom.comp ρ.asGroupHom
  have hφinj : Function.Injective φ :=
    (Matrix.GeneralLinearGroup.toLin' b).symm.injective.comp hρinj
  have hcardD : Nat.card D = 6 := RankOneThreeGroupAssembly.isSL2Two_card hD.1
  have hcardE : Nat.card E = 6 := RankOneThreeGroupAssembly.isSL2Two_card hE.1
  have hcardK : Nat.card K ≤ 6 := by
    have hdiv := Subgroup.card_dvd_of_injective φ hφinj
    have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) = 6 := by
      rw [Matrix.card_GL_field]
      norm_num [Fin.prod_univ_succ]
    rw [hGL] at hdiv
    exact Nat.le_of_dvd (by norm_num) hdiv
  have hDK : D = K := Subgroup.eq_of_le_of_card_ge le_sup_left (by simpa [hcardD] using hcardK)
  have hEK : E = K := Subgroup.eq_of_le_of_card_ge le_sup_right (by simpa [hcardE] using hcardK)
  exact hDK.trans hEK.symm

end Stellmacher.SectionOne

