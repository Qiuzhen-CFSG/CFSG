module

public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels
public import CFSG.Quasithin.ClassificationModels.Families
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Cyclic three-subgroups in the actual rank-one Borels

The concrete linear, unitary and Suzuki Borels have a normal Sylow two-subgroup
and a cyclic torus supplement. Their quotient by that Sylow subgroup is cyclic,
and every three-subgroup injects into this quotient. Sylow conjugacy and the
actual model equivalences transport the conclusion to each Bender model.
For PSU₃ the matrix field has order (2^n)² and the specified Frobenius involution;
the Hermitian form is transported by the existing genuine basis equivalence.

These are the local model facts used to exclude rank one in the initial
parabolic selection of 15.3.35. They supplement the proper-overgroup theorem
already proved in Chapter F, retaining cyclicity of the concrete torus.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), Remark A.2.4,
printed p.33; F.1.2--3, pp.259--260; final proof of 15.3.35, p.1139.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.RankOne

private theorem cyclic_quotient_of_sup {H : Type*} [Group H]
    (N D : Subgroup H) [N.Normal] [IsCyclic D] (hs : N ⊔ D = ⊤) :
    IsCyclic (H ⧸ N) := by
  let q := QuotientGroup.mk' N
  have hm : D.map q = ⊤ := by
    have he := congrArg (Subgroup.map q) hs
    simpa [Subgroup.map_sup, q, map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] using he
  apply isCyclic_of_surjective (q.comp D.subtype)
  apply MonoidHom.range_eq_top.mp
  simpa [MonoidHom.range_comp] using hm

private theorem cyclic_three_of_sup {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H) (D : Subgroup H) (hD : D ≤ normalizer ((T : Subgroup H) : Set H))
    (hcyc : IsCyclic D) (hs : (T : Subgroup H) ⊔ D = normalizer ((T : Subgroup H) : Set H))
    (A : Subgroup H) (hA : IsPGroup 3 A) (hAN : A ≤ normalizer ((T : Subgroup H) : Set H)) :
    IsCyclic A := by
  let B := normalizer ((T : Subgroup H) : Set H)
  let N := (T : Subgroup H).subgroupOf B
  let C := D.subgroupOf B
  let : IsCyclic D := hcyc
  let : N.Normal := (T : Subgroup H).normal_in_normalizer
  let : IsCyclic C := (subgroupOfEquivOfLe hD).isCyclic.mpr hcyc
  let : IsCyclic (B ⧸ N) := cyclic_quotient_of_sup N C (by
    change (T : Subgroup H).subgroupOf B ⊔ D.subgroupOf B = ⊤
    rw [← subgroupOf_sup (T : Subgroup H).le_normalizer hD, hs]
    exact subgroupOf_self _)
  let q := QuotientGroup.mk' N
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact T.isPGroup'.comap_subtype
  obtain ⟨n, hn⟩ := hk.exists_card_eq
  have hi := injective_comp_subtype_of_coprime_ker q
    (by rw [hn]; exact (by decide : Nat.Coprime 3 2).pow_right n)
    (A.subgroupOf B) hA.comap_subtype
  have hc : IsCyclic (A.subgroupOf B) := isCyclic_of_injective _ hi
  exact (subgroupOfEquivOfLe hAN).isCyclic.mp hc

private theorem transport {H K : Type*} [Group H] [Group K]
    (e : H ≃* K) (S : Sylow 2 H) (T : Sylow 2 K)
    (he : (S : Subgroup H).map e.toMonoidHom = (T : Subgroup K))
    (h : ∀ A : Subgroup H, IsPGroup 3 A → A ≤ normalizer ((S : Subgroup H) : Set H) → IsCyclic A) :
    ∀ A : Subgroup K, IsPGroup 3 A → A ≤ normalizer ((T : Subgroup K) : Set K) → IsCyclic A := by
  intro A hA hAN
  have hpre : A.comap e.toMonoidHom ≤ normalizer ((S : Subgroup H) : Set H) := by
    have hn := map_equiv_normalizer_eq (S : Subgroup H) e
    rw [he] at hn
    have hi := comap_mono (f := e.toMonoidHom) hAN
    rw [← hn, comap_map_eq_self_of_injective e.injective] at hi
    exact hi
  have hc := h (A.comap e.toMonoidHom) (hA.comap_of_injective _ e.injective) hpre
  let := hc
  exact isCyclic_of_surjective (e.toMonoidHom.subgroupComap A)
    (e.toMonoidHom.subgroupComap_surjective_of_surjective A e.surjective)

private theorem all_sylows {H : Type*} [Group H] [Finite H]
    (S : Sylow 2 H)
    (h : ∀ A : Subgroup H, IsPGroup 3 A → A ≤ normalizer ((S : Subgroup H) : Set H) → IsCyclic A)
    (T : Sylow 2 H) :
    ∀ A : Subgroup H, IsPGroup 3 A → A ≤ normalizer ((T : Subgroup H) : Set H) → IsCyclic A := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H S T
  exact transport (MulAut.conj g) S T (congrArg Sylow.toSubgroup hg) h

set_option backward.isDefEq.respectTransparency false in
private theorem of_equiv {H K : Type*} [Group H] [Group K] [Finite H]
    (e : H ≃* K) (T : Sylow 2 H)
    (h : ∀ A : Subgroup K, IsPGroup 3 A →
      A ≤ normalizer ((T.mapSurjective (f := e.toMonoidHom) e.surjective : Subgroup K) : Set K) →
        IsCyclic A) :
    ∀ A : Subgroup H, IsPGroup 3 A → A ≤ normalizer ((T : Subgroup H) : Set H) → IsCyclic A := by
  apply transport e.symm (T.mapSurjective (f := e.toMonoidHom) e.surjective) T _ h
  rw [Sylow.coe_mapSurjective, Subgroup.map_map]
  have hi : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id H := by
    ext x
    exact e.symm_apply_apply x
  rw [hi, Subgroup.map_id]

open BenderSuzuki.Converse ChapterF.Source.Linear in
private theorem linear {F : Type*} [Field F] [Finite F] [CharP F 2]
    (T : Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) :
    ∀ A : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F), IsPGroup 3 A →
      A ≤ normalizer ((T : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) : Set _) → IsCyclic A := by
  let e := MulEquiv.ofBijective (pi F) ⟨pi_injective, pi_surjective⟩
  let S := Matrix.SpecialLinearGroup.upperUnipotentSylow F 2
  have hS : (S : Subgroup (SL2 F)) = Unip F := unip_eq_upper.symm
  have hN : normalizer ((S : Subgroup (SL2 F)) : Set (SL2 F)) = Borel F := by
    rw [hS, unip_normalizer]
  have hc : IsCyclic (Torus F) := by
    rw [Torus_eq_range]
    exact isCyclic_of_surjective (torHom F).rangeRestrict (torHom F).rangeRestrict_surjective
  have h := cyclic_three_of_sup S (Torus F) (by rw [hN]; exact Torus_le_Borel) hc (by
    rw [hN, hS]; exact Unip_sup_Torus)
  exact all_sylows (S.mapSurjective e.surjective) (transport e S _ rfl h) T

open ChapterF.Source.Unitary in
private theorem unitary {F : Type*} [Field F] [Finite F]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (T : Sylow 2 (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∀ A : Subgroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J), IsPGroup 3 A →
      A ≤ normalizer ((T : Subgroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)) : Set _) → IsCyclic A := by
  obtain ⟨C, hC⟩ := FormTransport.exists_standard_basis J n hn hcard hconj
  let e := FormTransport.projectiveEquiv J C hC
  let J0 := FormTransport.standardForm J
  let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J0) :=
    Finite.of_surjective _ (ChapterF.Source.Unitary.suProjection_surjective J0)
  obtain ⟨_, _, S, ⟨D, hD, _, hc, _, hs⟩, _⟩ :=
    ChapterF.Source.Unitary.standard_psu_borel_data J0 n hn hcard hconj rfl
  let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective _ (ChapterF.Source.Unitary.suProjection_surjective J)
  exact of_equiv e T (all_sylows S (cyclic_three_of_sup S D hD hc hs) _)

open BenderSuzuki.MatrixGroups in
private theorem suzuki (m : ℕ) (hm : 0 < m)
    (T : Sylow 2 (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) :
    ∀ A : Subgroup (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m), IsPGroup 3 A →
      A ≤ normalizer ((T : Subgroup (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) : Set _) → IsCyclic A := by
  obtain ⟨S, hS⟩ := suzukiRootSubgroup_isSylow m hm
  have hN : normalizer ((S : Subgroup (SuzukiMatrixGroup m)) : Set (SuzukiMatrixGroup m)) = SuzukiBorelSubgroup m := by
    rw [hS, suzukiRootSubgroup_normalizer m hm]
  exact all_sylows S (cyclic_three_of_sup S (SuzukiSplitTorus m)
    (by rw [hN, suzukiBorelSubgroup_eq_sup]; exact le_sup_right)
    (suzukiSplitTorus_isCyclic m hm)
    (by rw [hN, hS, suzukiBorelSubgroup_eq_sup])) T

/-- Every three-subgroup of a Borel in an actual Bender model is cyclic. -/
theorem bender_borel_three_cyclic {H : Type*} [Group H] [Finite H]
    (hm : ClassificationModels.IsBenderModel H) (T : Sylow 2 H)
    (A : Subgroup H) (hA : IsPGroup 3 A) (hAN : A ≤ normalizer ((T : Subgroup H) : Set H)) :
    IsCyclic A := by
  cases hm with
  | linear n hn hi =>
    obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hi
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    exact of_equiv e T (linear _) A hA hAN
  | unitary n hn hi =>
    obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := hi
    exact of_equiv e T (unitary J n (by omega) hcard hconj _) A hA hAN
  | suzuki m hm hi =>
    obtain ⟨e⟩ := hi
    exact of_equiv e T (suzuki m (by omega) _) A hA hAN

/-- Proper Sylow overgroups in a Bender model lie in the actual Borel. -/
theorem bender_borel_facts {H : Type*} [Group H]
    (hm : ClassificationModels.IsBenderModel H) (T : Sylow 2 H) :
    ChapterF.Source.RankOneSylowFacts T := by
  apply ChapterF.Source.IsRankOneModel.rankOneSylowFacts _ T
  cases hm with
  | linear n hn hi => exact .linear n (by omega) hi
  | unitary n hn hi => exact .projective_unitary n (by omega) hi
  | suzuki m _ hi => exact .suzuki m hi

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.RankOne
