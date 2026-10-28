module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankOne.CentralImage
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.PResidual.SubnormalSupplement

/-!
# Small Sylow pairs in characteristic-two PSU₃

The natural unitary action makes a Sylow two-subgroup regular off its fixed
point. If a permuting subgroup A and that Sylow generated the whole group,
A would be transitive on the natural points. For |A| ≤ 27 and fixed-field
order at least four, this contradicts the Sylow order q³ ≥ 64. Thus their
join is proper. The proved root-generation theorem places this join in the
Borel. Its cyclic Cartan supplement then makes every three-subgroup cyclic,
since the quotient by the normal Sylow two-subgroup is injective on it.

Sylow conjugacy and the actual change-of-Hermitian-basis equivalence retain
both the normalizer containment and cyclicity for every published PSU₃
model. No normalization is inferred from permutability alone.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528), using the genuine rank-one Borel theorem F.1.3(1), pp.259–260,
and the natural action of Huppert II.10.12.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankOne
open CFSG.Quasithin.ChapterF.Source

private theorem small_pair_proper {G Ω : Type*} [Group G] [Finite G] [Finite Ω]
    (S : Sylow 2 G) (A : Subgroup G) (rho : G →* Equiv.Perm Ω) (α β : Ω)
    (hfix : ∀ s : S, rho s α = α)
    (htrans : ∀ y : Ω, ∃ g : G, rho g α = y)
    (hfree : Function.Injective (fun s : S => rho s β))
    (hsmall : Nat.card A < Nat.card S)
    (hperm : (A : Set G) * (S : Set G) = (S : Set G) * (A : Set G)) :
    A ⊔ (S : Subgroup G) < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro htop
  have hprod := coe_sup_of_set_mul_comm A (S : Subgroup G) hperm
  rw [htop, coe_top] at hprod
  have hsurj : Function.Surjective (fun a : A => rho a α) := by
    intro y
    obtain ⟨g, hg⟩ := htrans y
    obtain ⟨a, ha, s, hs, he⟩ := show g ∈ (A : Set G) * (S : Set G) from
      hprod ▸ Set.mem_univ g
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [← he, map_mul, Equiv.Perm.coe_mul, Function.comp_apply,
      hfix ⟨s, hs⟩] at hg
    exact hg
  exact (not_lt_of_ge ((Nat.card_le_card_of_injective _ hfree).trans
    (Nat.card_le_card_of_surjective _ hsurj))) hsmall

private theorem cyclic_of_cyclic_supplement {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (D A : Subgroup G)
    (hD : D ≤ normalizer (S : Set G)) (hc : IsCyclic D)
    (hsup : (S : Subgroup G) ⊔ D = normalizer (S : Set G))
    (hA : IsPGroup 3 A) (hAN : A ≤ normalizer (S : Set G)) : IsCyclic A := by
  let B := normalizer (S : Set G)
  let U := (S : Subgroup G).subgroupOf B
  let E := D.subgroupOf B
  let _ : U.Normal := normal_subgroupOf_of_le_normalizer (le_refl B)
  let _ : IsCyclic E := (subgroupOfEquivOfLe hD).isCyclic.mpr hc
  have hUE : U ⊔ E = ⊤ := by
    change (S : Subgroup G).subgroupOf B ⊔ D.subgroupOf B = ⊤
    rw [← subgroupOf_sup (show (S : Subgroup G) ≤ B from
      (S : Subgroup G).le_normalizer) hD, hsup]
    exact subgroupOf_self B
  let q := QuotientGroup.mk' U
  have hsurj : Function.Surjective (q.comp E.subtype) := by
    intro z
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective U z
    obtain ⟨s, hs, d, hd, rfl⟩ := mem_sup_of_normal_left.mp (hUE ▸ mem_top b)
    refine ⟨⟨d, hd⟩, ?_⟩
    change q d = q (s * d)
    rw [map_mul, show q s = 1 from (QuotientGroup.eq_one_iff s).mpr hs, one_mul]
  let _ : IsCyclic (B ⧸ U) := isCyclic_of_surjective (q.comp E.subtype) hsurj
  have hcyc : IsCyclic (A.subgroupOf B) := by
    apply isCyclic_of_injective (q.comp (A.subgroupOf B).subtype)
    apply injective_comp_subtype_of_coprime_ker q _ _ hA.comap_subtype
    rw [QuotientGroup.ker_mk']
    have hU : IsPGroup 2 U := S.isPGroup'.comap_subtype
    obtain ⟨n, hn⟩ := hU.exists_card_eq
    change Nat.Coprime 3 (Nat.card U)
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  exact (subgroupOfEquivOfLe hAN).isCyclic.mp hcyc

private def SmallPairBorel {G : Type*} [Group G] (S : Sylow 2 G) : Prop :=
  ∀ A : Subgroup G, IsPGroup 3 A → Nat.card A ≤ 27 →
    (A : Set G) * (S : Set G) = (S : Set G) * (A : Set G) →
      A ≤ normalizer (S : Set G) ∧ IsCyclic A

private theorem smallPairBorel_transport {G H : Type*} [Group G] [Finite G] [Group H]
    (S : Sylow 2 G) (T : Sylow 2 H) (e : G ≃* H)
    (hST : (S : Subgroup G).map e.toMonoidHom = (T : Subgroup H))
    (hT : SmallPairBorel T) : SmallPairBorel S := by
  intro A hA hcard hperm
  have hp : (A.map e.toMonoidHom : Set H) * (T : Set H) =
      (T : Set H) * (A.map e.toMonoidHom : Set H) := by
    have hh := congrArg (fun s : Set G => e.toMonoidHom '' s) hperm
    change (A.map e.toMonoidHom : Set H) * ((T : Subgroup H) : Set H) =
      ((T : Subgroup H) : Set H) * (A.map e.toMonoidHom : Set H)
    rw [← hST]
    simpa only [coe_map, Sylow.coe_coe, Set.image_mul] using hh
  have hc : Nat.card (A.map e.toMonoidHom) ≤ 27 := by
    rw [← Nat.card_congr (A.equivMapOfInjective e.toMonoidHom e.injective).toEquiv]
    exact hcard
  obtain ⟨hAN, hcyc⟩ := hT _ (hA.map _) hc hp
  refine ⟨?_, (A.equivMapOfInjective e.toMonoidHom e.injective).isCyclic.mpr hcyc⟩
  apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
  have hn := map_equiv_normalizer_eq (S : Subgroup G) e
  rw [hST] at hn
  change A.map e.toMonoidHom ≤ (normalizer ((S : Subgroup G) : Set G)).map e.toMonoidHom
  rw [hn]
  exact hAN

private theorem smallPairBorel_all_sylows {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (hS : SmallPairBorel S) (T : Sylow 2 G) : SmallPairBorel T := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  exact smallPairBorel_transport T S (MulAut.conj g)
    (congrArg Sylow.toSubgroup hg) hS

open BenderSuzuki.MatrixGroups
open scoped Matrix

private theorem standard_unitary_smallPairBorel {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card F = (2 ^ f) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ f))
    (hstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) : SmallPairBorel T := by
  let _ := Fintype.ofFinite F
  let _ : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective _ (Unitary.suProjection_surjective J)
  obtain ⟨rho, α, S, ⟨D, hD, _, hcyc, _, hsup⟩, hproper, _, _, _, hScard, hN,
    hregular, htwo⟩ := Unitary.standard_psu_borel_data J f (by omega) hcard hconj hstandard
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ normalizer (S : Set G) := by
    by_contra! hh
    exact hproper.ne (eq_top_iff.mpr fun x _ => hh x)
  let β := rho g α
  have hβα : β ≠ α := by
    intro he
    apply hg
    change g ∈ normalizer ((S : Subgroup G) : Set G)
    rw [hN]
    exact he
  have hfix (s : S) : rho s α = α := by
    have hs := (S : Subgroup G).le_normalizer s.property
    rw [hN] at hs
    exact hs
  have htrans : ∀ y, ∃ a : G, rho a α = y := by
    intro y
    by_cases hy : y = α
    · exact ⟨1, by simp [hy]⟩
    · obtain ⟨a, ha, _⟩ := htwo α β y α hβα.symm hy
      exact ⟨a, ha⟩
  have hfree : Function.Injective (fun s : S => rho s β) := by
    intro s t he
    have hsne : rho (s : G) β ≠ α := by
      intro hs
      apply hβα
      have hsi := hfix s⁻¹
      have heq := congrArg (rho (s⁻¹ : S)) hs
      rw [hsi] at heq
      simpa using heq
    obtain ⟨r, _, hu⟩ := hregular β (rho (s : G) β) hβα hsne
    exact (hu s rfl).trans (hu t he.symm).symm
  apply smallPairBorel_all_sylows S _ T
  intro A hA hAc hperm
  have hlarge : 27 < Nat.card S := by
    rw [hScard]
    have hq : 4 ≤ 2 ^ f := (show 2 ^ 2 ≤ 2 ^ f from Nat.pow_le_pow_right (by decide) hf)
    nlinarith
  have hAN : A ≤ normalizer (S : Set G) := le_sup_left.trans
    ((Unitary.standard_psu_facts J f (by omega) hcard hconj hstandard S).unique_maximal
      _ le_sup_right (small_pair_proper S A rho α β hfix htrans hfree
        (hAc.trans_lt hlarge) hperm))
  exact ⟨hAN, cyclic_of_cyclic_supplement S D A hD hcyc hsup hA hAN⟩

/-- A small three-subgroup permuting with a genuine Sylow in PSU₃(2^f)
lies in its Borel and embeds in the cyclic Cartan quotient. -/
theorem unitary_smallPair_borel {G : Type*} [Group G] [Finite G]
    {f : ℕ} (hf : 2 ≤ f) (hmodel : ClassicalGroup.IsPSU G 3 (2 ^ f))
    (S : Sylow 2 G) (A : Subgroup G) (hA : IsPGroup 3 A) (hcardA : Nat.card A ≤ 27)
    (hperm : (A : Set G) * (S : Set G) = (S : Set G) * (A : Set G)) :
    A ≤ normalizer (S : Set G) ∧ IsCyclic A := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := hmodel
  obtain ⟨C, hC⟩ := Unitary.FormTransport.exists_standard_basis J f (by omega) hcard hconj
  let e' := e.trans (Unitary.FormTransport.projectiveEquiv J C hC)
  exact smallPairBorel_transport S (S.mapSurjective (f := e'.toMonoidHom) e'.surjective)
    e' rfl (standard_unitary_smallPairBorel (Unitary.FormTransport.standardForm J)
      f hf hcard hconj rfl _) A hA hcardA hperm

theorem unitary_smallPair_isCyclic {G : Type*} [Group G] [Finite G]
    {f : ℕ} (hf : 2 ≤ f) (hmodel : ClassicalGroup.IsPSU G 3 (2 ^ f))
    (S : Sylow 2 G) (A : Subgroup G) (hA : IsPGroup 3 A) (hcardA : Nat.card A ≤ 27)
    (hperm : (A : Set G) * (S : Set G) = (S : Set G) * (A : Set G)) : IsCyclic A :=
  (unitary_smallPair_borel hf hmodel S A hA hcardA hperm).2

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankOne
