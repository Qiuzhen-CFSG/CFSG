module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.IndexEstimates
public import Theory.Representation.RankOne.QuadraticRecognition.TwoRankOne

/-!
# The dihedral row in the reciprocal intersection comparison

The source list includes D₁₀, outside the Chapter 5 module catalogue.
The actual local quotient is core-free. A kernel of its center action
would either be a normal two-subgroup or contain O², the latter contradicting
the proved residual fixed-space vanishing. Thus this action is faithful.

D₁₀ has two-rank one and more than three involutions. The existing binary
transvection argument makes every nontrivial elementary actor have fixed
index at least four. Identity coordinates transport the bound back to the
original moving center. `ReciprocalCatalogue` compares it with the upper
bound two under reverse containment, excluding the dihedral intersection.

Source: DGS, *Groups and Graphs* (1985), the Hypothesis B′ model list and
(8.2), pp.134--135. No Chapter 5 theorem is extended by a family tag.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial

private theorem dihedral_two_rank : primeRank 2 (DihedralGroup 5) ≤ 1 := by
  let S : Sylow 2 (DihedralGroup 5) := Sylow.ofCard (zpowers (DihedralGroup.sr 0 : DihedralGroup 5)) (by
    rw [Nat.card_zpowers,DihedralGroup.orderOf_sr,DihedralGroup.nat_card]
    rw [Nat.factorization_mul (by decide) (by decide),
      Nat.prime_two.factorization,Nat.prime_five.factorization]
    norm_num)
  exact S.primeRank_le_one_of_isCyclic
    (inferInstanceAs (IsCyclic (zpowers (DihedralGroup.sr 0 : DihedralGroup 5))))

private theorem dihedral_action_faithful {L W : Type*} [Group L] [Finite L]
    [AddCommGroup W] [Module (ZMod 2) W] [Nontrivial W]
    (e : (L ⧸ pCore 2 L) ≃* DihedralGroup 5)
    (ρ : Representation (ZMod 2) (DihedralGroup 5) W)
    (hres : fixedSpace ρ (pResidual 2 (DihedralGroup 5)) = ⊥) : Function.Injective ρ := by
  have hnot : ¬ pResidual 2 (DihedralGroup 5) ≤ ρ.ker := by
    intro h
    have he : fixedSpace ρ (pResidual 2 (DihedralGroup 5)) = ⊤ := by
      apply top_unique
      intro v _ g
      change ρ g v = v
      rw [show ρ g = 1 from h g.property]
      rfl
    exact top_ne_bot (he.symm.trans hres)
  apply ρ.ker_eq_bot_iff.mp
  by_cases hd : 5 ∣ Nat.card ρ.ker
  · have hi : ρ.ker.index ∣ 2 := by
      apply Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < 5)
      have hm := Nat.mul_dvd_mul_right hd ρ.ker.index
      rw [ρ.ker.card_mul_index,DihedralGroup.nat_card,mul_comm 5 ρ.ker.index] at hm
      exact hm
    have hp : IsPGroup 2 ((DihedralGroup 5) ⧸ ρ.ker) :=
      IsPGroup.of_card_dvd_pow (n := 1) (by simpa only [pow_one,←Subgroup.index_eq_card] using hi)
    exact (hnot ((pResidual_le_iff_isPGroup_quotient 2 ρ.ker).mpr hp)).elim
  · have hc : Nat.card ρ.ker ∣ 2 := by
      apply ((Nat.prime_five.coprime_iff_not_dvd.mpr hd).symm).dvd_of_dvd_mul_right
      simpa only [DihedralGroup.nat_card] using ρ.ker.card_subgroup_dvd_card
    have hp : IsPGroup 2 ρ.ker := IsPGroup.of_card_dvd_pow (n := 1) (by simpa using hc)
    have hk : ρ.ker ≤ pCore 2 (DihedralGroup 5) := le_sSup ⟨inferInstance,hp⟩
    have hcore : pCore 2 (DihedralGroup 5) = ⊥ := by
      rw [←pCore_map_iso 2 e,Subgroup.pCore_quotient_pCore_eq_bot,Subgroup.map_bot]
    exact bot_unique (hk.trans hcore.le)

private theorem dihedral_elementary_fixed_bound {W : Type*}
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (DihedralGroup 5) W) (hf : Function.Injective ρ)
    (A : Subgroup (DihedralGroup 5)) [IsElementaryAbelian 2 A] (hne : A ≠ ⊥) :
    4 ≤ Nat.card (W ⧸ fixedSpace ρ A) := by
  obtain ⟨a,ha,ha1⟩ := A.bot_or_exists_ne_one.resolve_left hne
  have hd := involution_fixedCodim_ge_two_of_two_rank_one dihedral_two_rank
    (DihedralGroup.sr 0) (DihedralGroup.sr 1) (DihedralGroup.sr 3)
    (by constructor <;> decide) (by constructor <;> decide) (by constructor <;> decide)
    (by decide) (by decide) (by decide) (by decide)
    ρ hf a ⟨ha1,elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha⟩
  have hlo : 4 ≤ Nat.card (W ⧸ fixedSpace ρ (zpowers a)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hd
  have hle : Nat.card (W ⧸ fixedSpace ρ (zpowers a)) ≤ Nat.card (W ⧸ fixedSpace ρ A) := by
    let : Finite (W ⧸ fixedSpace ρ A) := Finite.of_surjective _ (fixedSpace ρ A).mkQ_surjective
    exact Nat.card_le_card_of_surjective _
      (Submodule.factor_surjective (fixedSpace_antitone ρ (zpowers_le.mpr ha)))
  exact hlo.trans hle


open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Every elementary actor escaping the core at the moving dihedral vertex
moves at least four vectors, using the separate D₁₀ transvection argument. -/
theorem source_moving_dihedral_field_square_bound (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥)
    (e : (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≃* DihedralGroup 5)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAL : A ≤ d.localGroup w.val)
    (hAQ : ¬ A ≤ Q (family P) w.val) :
    4 ≤ (centralizer (A : Set G)).relIndex (Z (family P) w.val) := by
  let := finite_endpoints h
  let := CommutingOneProfile.source_center_elementary h w.val
  let := source_center_nontrivial h w.val
  let F := family P
  let L := d.localGroup w.val
  let Z₀ := Z F w.val
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let : Finite L := Finite.of_injective (inclusion (d.local_le w.val)) (inclusion_injective _)
  let : Finite Z₀ := Finite.of_injective (inclusion (Z_le_stabilizer F w.val)) (inclusion_injective _)
  obtain ⟨ρ,S,hact,_,_,_,_,hres,_⟩ := source_moving_center_module h d hc hab hd hb hcomm w hm e
  have hf := dihedral_action_faithful e ρ hres
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  let : IsElementaryAbelian 2 ((A.subgroupOf L).map q) := IsElementaryAbelian.map q
  have hne : (A.subgroupOf L).map q ≠ ⊥ := by
    intro he
    have hk := (Subgroup.map_eq_bot_iff _).mp he
    rw [local_quotient_kernel F d w.val e] at hk
    exact hAQ (fun a ha => hk (show (⟨a,hAL ha⟩ : L) ∈ A.subgroupOf L from ha))
  have hbound := dihedral_elementary_fixed_bound ρ hf _ hne
  have hZL : Z₀ ≤ L := pGroup_le_localGroup F d w.val _
    (IsElementaryAbelian.isPGroup 2 _) (Z_le_stabilizer F w.val)
  have hi := center_action_fixed_index L Z₀ A hZL
    ((d.local_le w.val).trans (stabilizer_normalizes_Z F w.val)) hAL q ρ hact
  rwa [hi] at hbound


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
