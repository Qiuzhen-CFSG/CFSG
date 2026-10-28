module

public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.QuotientGeometry
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Lifting.Transport
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.StandardAction
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.SpecialBorel
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.RootGeneration
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.FormTransport

/-!
# The concrete SU₃ and PSU₃ branches of F.1.3(1)

Source: Aschbacher–Smith, `refs/quasithin.pdf`, printed pp.259–260,
Remark F.1.2 and Lemma F.1.3(1). The matrix field has order q², where
q = 2^n is the fixed-field order. Every positive n, including n = 1, is covered.

The standard SU₃ root group is Sylow. Its normalizer is the root–torus
Borel, which is proper and solvable and has a cyclic odd-order complement.
Generation by distinct conjugate roots forces every proper Sylow overgroup
into this Borel. The general Sylow-normalizer calculation supplies its 2-core.

For PSU₃, proper-overgroup uniqueness descends through the actual surjection
SU₃ → PSU₃, and the natural isotropic-point action supplies its Borel structure.
The scalar kernel is handled by the special-Borel calculation; a root group is
never identified with its full projective preimage. Actual matrix conjugation
transports arbitrary Hermitian forms to the antidiagonal form. Sylow conjugacy
then gives every Sylow subgroup, together with an explicit matrix Borel formula.
-/

open BenderSuzuki.MatrixGroups BenderSuzuki.External
open scoped Matrix

namespace CFSG.Quasithin.ChapterF.Source.Unitary

/-- The local normalizer clauses for a standard PSU₃ Sylow subgroup. -/
public theorem standard_psu_sylow_structure
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    ∃ T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
      Subgroup.normalizer (T : Set (ProjectiveSpecialUnitaryMatrixGroup J)) < ⊤ ∧
      twoCore (Subgroup.normalizer (T : Set (ProjectiveSpecialUnitaryMatrixGroup J))) =
        (T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ∧
      Group.IsSolvable (Subgroup.normalizer
        (T : Set (ProjectiveSpecialUnitaryMatrixGroup J))) ∧
      ∃ D : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J),
        D ≤ Subgroup.normalizer (T : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ∧
        Nat.Coprime 2 (Nat.card D) ∧ IsMulCommutative D ∧
        Disjoint (T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) D ∧
        (T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ⊔ D =
          Subgroup.normalizer (T : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  obtain ⟨_, _, T, ⟨D, hD, hcop, hcyc, hdis, hsup⟩, hproper, hsolv, _⟩ :=
    standard_psu_borel_data J n hn hcard hconj hstandard
  have : IsCyclic D := hcyc
  exact ⟨T, hproper, twoCore_sylow_normalizer T, hsolv,
    D, hD, hcop, inferInstance, hdis, hsup⟩

private theorem proper_overgroup_of_generation {G : Type*} [Group G]
    (R : Subgroup G)
    (hgen : ∀ g : G, g ∉ Subgroup.normalizer R →
      R ⊔ R.map (MulAut.conj g).toMonoidHom = ⊤)
    (M : Subgroup G) (hRM : R ≤ M) (hM : M < ⊤) :
    M ≤ Subgroup.normalizer R := by
  intro g hg
  by_contra hn
  apply hM.ne
  apply top_unique
  rw [← hgen g hn]
  refine sup_le hRM ?_
  rintro _ ⟨x, hx, rfl⟩
  exact M.mul_mem (M.mul_mem hg (hRM hx)) (M.inv_mem hg)

private theorem all_sylows {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (hS : RankOneSylowFacts S) (T : Sylow 2 G) :
    RankOneSylowFacts T := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
  have hm : S.mapSurjective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).surjective = T := by
    apply Sylow.ext
    exact congrArg Sylow.toSubgroup hg
  exact hm ▸ rankOneSylowFacts_map S (MulAut.conj g) hS

/-- Every Sylow of the standard SU₃ has the full rank-one Borel structure. -/
public theorem standard_su_facts
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (T : Sylow 2 J.specialSubgroup) : RankOneSylowFacts T := by
  obtain ⟨_, _, S, hSR, _, _, _, hN, _, hproper, hsolv, hdis, hcyc, _, hodd⟩ :=
    standard_su_borel_data J n hn hcard hconj hstandard
  apply all_sylows S ?_ T
  refine ⟨?_, ?_, twoCore_sylow_normalizer S, ?_, ?_⟩
  · change Subgroup.normalizer ((S : Subgroup J.specialSubgroup) : Set J.specialSubgroup) < ⊤
    rwa [hSR]
  · intro M hSM hM
    change M ≤ Subgroup.normalizer ((S : Subgroup J.specialSubgroup) : Set _)
    rw [hSR] at hSM ⊢
    exact proper_overgroup_of_generation _
      (su_root_generation J hstandard n hn hcard hconj) M hSM hM
  · change Group.IsSolvable
      (Subgroup.normalizer ((S : Subgroup J.specialSubgroup) : Set J.specialSubgroup))
    rwa [hSR]
  · have : IsCyclic (suTorus J hstandard) := hcyc
    refine ⟨suTorus J hstandard, ?_, Nat.coprime_two_left.mpr hodd,
      inferInstance, ?_, ?_⟩
    · change suTorus J hstandard ≤
        Subgroup.normalizer ((S : Subgroup J.specialSubgroup) : Set _)
      rw [hSR, hN]
      exact le_sup_right
    · simpa only [hSR] using hdis
    · change (S : Subgroup J.specialSubgroup) ⊔ suTorus J hstandard =
        Subgroup.normalizer ((S : Subgroup J.specialSubgroup) : Set _)
      simpa only [hSR] using hN.symm

private theorem unique_maximal_map {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (S : Sylow 2 G)
    (hS : RankOneSylowFacts S)
    (M : Subgroup H) (hSM : (S : Subgroup G).map f ≤ M) (hM : M < ⊤) :
    M ≤ Subgroup.normalizer ((S : Subgroup G).map f : Set H) := by
  have hpre : M.comap f < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro he
    apply hM.ne
    have hh := congrArg (Subgroup.map f) he
    simpa only [Subgroup.map_comap_eq_self_of_surjective hf,
      Subgroup.map_top_of_surjective f hf] using hh
  have hh := Subgroup.map_mono (f := f)
    (hS.unique_maximal (M.comap f) (Subgroup.map_le_iff_le_comap.mp hSM) hpre)
  rw [Subgroup.map_comap_eq_self_of_surjective hf] at hh
  exact hh.trans (Subgroup.le_normalizer_map f)

/-- Every Sylow of the standard PSU₃ has the full rank-one Borel structure.
Proper-overgroup uniqueness descends from SU₃ along the genuine projection. -/
public theorem standard_psu_facts
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    RankOneSylowFacts T := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective _ (suProjection_surjective J)
  obtain ⟨S, hp, hc, hs, hd⟩ := standard_psu_sylow_structure J n hn hcard hconj hstandard
  apply all_sylows S ?_ T
  refine ⟨hp, ?_, hc, hs, hd⟩
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective (suProjection_surjective J) 2 S
  intro M hSM hM
  subst S
  exact unique_maximal_map (suProjection J) (suProjection_surjective J) P
    (standard_su_facts J n hn hcard hconj hstandard P) M hSM hM

private theorem normalizer_eq_conjugate_borel {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] (e : G ≃* H) (T : Sylow 2 G) (S : Sylow 2 H)
    (B : Subgroup H) (hB : Subgroup.normalizer (S : Set H) = B) :
    ∃ g : H, Subgroup.normalizer (T : Set G) =
      (B.map (MulAut.conj g).toMonoidHom).comap e.toMonoidHom := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H S
    (T.mapSurjective (f := e.toMonoidHom) e.surjective)
  have hm : (S : Subgroup H).map (MulAut.conj g).toMonoidHom =
      (T : Subgroup G).map e.toMonoidHom := congrArg Sylow.toSubgroup hg
  have hh := Subgroup.map_equiv_normalizer_eq (S : Subgroup H) (MulAut.conj g)
  change (Subgroup.normalizer (S : Set H)).map (MulAut.conj g).toMonoidHom = _ at hh
  rw [hB, hm, ← Subgroup.map_equiv_normalizer_eq (T : Subgroup G) e] at hh
  refine ⟨g, ?_⟩
  rw [hh, Subgroup.comap_map_eq_self_of_injective e.injective]
  rfl

/-- For an arbitrary Hermitian form and Sylow subgroup, the SU₃ normalizer is
a conjugate of the concrete root–torus Borel, transported by an actual basis matrix. -/
public theorem su_sylow_normalizer_eq_matrix_borel
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) (T : Sylow 2 J.specialSubgroup) :
    ∃ (C : GL (Fin 3) F)
      (hC : J.conjTranspose C.val * J.form * C.val = (FormTransport.standardForm J).form)
      (g : (FormTransport.standardForm J).specialSubgroup),
      Subgroup.normalizer (T : Set J.specialSubgroup) =
        ((suRoot (FormTransport.standardForm J) rfl ⊔
          suTorus (FormTransport.standardForm J) rfl).map (MulAut.conj g).toMonoidHom).comap
            (FormTransport.specialEquiv J C hC).toMonoidHom := by
  obtain ⟨C, hC⟩ := FormTransport.exists_standard_basis J n hn hcard hconj
  obtain ⟨_, _, S, hSR, _, _, _, hN, _⟩ :=
    standard_su_borel_data (FormTransport.standardForm J) n hn hcard hconj rfl
  have hB : Subgroup.normalizer (S : Set (FormTransport.standardForm J).specialSubgroup) =
      suRoot (FormTransport.standardForm J) rfl ⊔ suTorus (FormTransport.standardForm J) rfl := by
    change Subgroup.normalizer ((S : Subgroup (FormTransport.standardForm J).specialSubgroup) :
      Set (FormTransport.standardForm J).specialSubgroup) = _
    rwa [hSR]
  obtain ⟨g, hg⟩ := normalizer_eq_conjugate_borel
    (FormTransport.specialEquiv J C hC) T S _ hB
  exact ⟨C, hC, g, hg⟩

/-- For an arbitrary Hermitian form and Sylow subgroup, the PSU₃ normalizer is
a conjugate of the projective matrix Borel, transported by the induced PGL conjugation. -/
public theorem psu_sylow_normalizer_eq_matrix_borel
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ (C : GL (Fin 3) F)
      (hC : J.conjTranspose C.val * J.form * C.val = (FormTransport.standardForm J).form)
      (g : ProjectiveSpecialUnitaryMatrixGroup (FormTransport.standardForm J)),
      Subgroup.normalizer (T : Set (ProjectiveSpecialUnitaryMatrixGroup J)) =
        (((hermitianUnipotentPSU (FormTransport.standardForm J) rfl).range ⊔
          (hermitianTorusPSU (FormTransport.standardForm J) rfl).range).map
            (MulAut.conj g).toMonoidHom).comap (FormTransport.projectiveEquiv J C hC).toMonoidHom := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective _ (suProjection_surjective J)
  let J0 := FormTransport.standardForm J
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J0) :=
    Finite.of_surjective _ (suProjection_surjective J0)
  obtain ⟨C, hC⟩ := FormTransport.exists_standard_basis J n hn hcard hconj
  obtain ⟨_, _, S, hSR, _⟩ := standard_su_borel_data J0 n hn hcard hconj rfl
  let P := S.mapSurjective (suProjection_surjective J0)
  have hP : (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J0)) =
      (hermitianUnipotentPSU J0 rfl).range := by
    change (S : Subgroup J0.specialSubgroup).map (suProjection J0) = _
    rw [hSR]
    exact suRoot_map_projection J0 (FormTransport.standardForm_form J)
  obtain ⟨_, _, _, _, _, _, hsup, hN, _⟩ :=
    standard_projective_matrix_borel J0 n hn hcard hconj rfl
  have hB : Subgroup.normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J0)) =
      (hermitianUnipotentPSU J0 rfl).range ⊔ (hermitianTorusPSU J0 rfl).range := by
    change Subgroup.normalizer ((P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J0)) :
      Set (ProjectiveSpecialUnitaryMatrixGroup J0)) = _
    rw [hP, hN, hsup]
  obtain ⟨g, hg⟩ := normalizer_eq_conjugate_borel
    (FormTransport.projectiveEquiv J C hC) T P _ hB
  exact ⟨C, hC, g, hg⟩

end CFSG.Quasithin.ChapterF.Source.Unitary

namespace CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.Unitary

/-- The concrete special-unitary branch of F.1.3(1), with matrix-field order
(2^n)² and the specified Frobenius involution, including n = 1. -/
public theorem rankOneSylowFacts_su3
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) (T : Sylow 2 J.specialSubgroup) :
    RankOneSylowFacts T := by
  obtain ⟨C, hC⟩ := FormTransport.exists_standard_basis J n hn hcard hconj
  apply rankOneSylowFacts_of_equiv T (FormTransport.specialEquiv J C hC)
  exact standard_su_facts (FormTransport.standardForm J) n hn hcard hconj rfl _

/-- The concrete projective-unitary branch of F.1.3(1), with matrix-field order
(2^n)² and the specified Frobenius involution, including n = 1. -/
public theorem rankOneSylowFacts_psu3
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) : RankOneSylowFacts T := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective _ (suProjection_surjective J)
  obtain ⟨C, hC⟩ := FormTransport.exists_standard_basis J n hn hcard hconj
  apply rankOneSylowFacts_of_equiv T (FormTransport.projectiveEquiv J C hC)
  exact standard_psu_facts (FormTransport.standardForm J) n hn hcard hconj rfl _

end CFSG.Quasithin.ChapterF.Source
