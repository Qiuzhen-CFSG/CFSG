module

public import CFSG.Quasithin.MainConverse.Transport
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Rank
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Core
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Coverage
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Linear
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Suzuki

/-!
# The Ree local clauses of the quasithin converse

The source target is QT and E for a finite nonabelian simple group isomorphic
to the genuine `ReeF4.Model m`, with `1 ≤ m`. QT bounds odd-prime ranks in
every two-local; E tests the intrinsic two-cores of maximal two-locals
containing a Sylow subgroup. The nonsimple full ²F₄(2) and the separately
constructed Tits simple group are outside this parameter range.

The full root-defined parabolics include the complementary torus. Their
Suzuki/SL₂-times-torus projections with two-group kernels give the rank bounds.
Coverage of two-subgroup normalizers gives QT; maximality, normalization of a
nonidentity root radical, and its intrinsic centralizer calculation give E.
The final reduction transports both conclusions along the actual model
isomorphism, including the local two-cores.

The assembly below discharges the projection maps, normalizer coverage,
nontriviality, relative normalization, and radical centralizers using the
concrete full-parabolic calculations. Thus QT and E hold for every actual
model isomorphism with `1 ≤ m`, without extra local or representation premises.
The separate `isQTKE_of_properK` interface retains proper K as the induction
hypothesis; it does not require standalone proper-section certification.
The earlier conditional reductions remain available with their original APIs.

Sources: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Theorem 0.1.2(1), printed p.4, repeated as Theorem
0.1.1 on p.482, and F.1.12(I)(5), p.263 (`refs/quasithin.pdf`); the coverage
route is the finite Borel–Tits theorem, GLS3 Theorem 3.1.3
(`refs/KGroup/GLS3/chapter3.tex`).
-/

namespace CFSG.Quasithin.MainConverse.ReeLocal

open Subgroup ReeF4 ReeF4.LargeLocalSeeds ReeF4.ConverseParabolics
open BenderSuzuki.MatrixGroups

/-- Normalizers of all nonidentity two-subgroups must be covered. The two
representation maps include the complementary parabolic torus. -/
public theorem quasithin_of_root_projections {m : ℕ} (hm : 1 ≤ m)
    (hcover : ∀ R : Subgroup (Model m), R ≠ ⊥ → IsPGroup 2 R →
      ∃ (g : Model m) (s : Side),
        (normalizer (R : Set (Model m))).map (MulAut.conj g).toMonoidHom ≤ parabolic m s)
    (πs : parabolic m .suzuki →* SuzukiMatrixGroup m × (CoefficientField m)ˣ)
    (hπs : IsPGroup 2 πs.ker)
    (πl : parabolic m .linear →*
      Matrix.SpecialLinearGroup (Fin 2) (CoefficientField m) × (CoefficientField m)ˣ)
    (hπl : IsPGroup 2 πl.ker) : IsQuasithin (Model m) := by
  apply Theory.GroupTheory.isQuasithin_iff_twoLocal.mpr
  rintro M ⟨R, hR, hpR, rfl⟩ p hp ho
  obtain ⟨g, s, hg⟩ := hcover R hR hpR
  rw [Theory.GroupTheory.primeRank_equiv p
    ((MulAut.conj g).subgroupMap (normalizer (R : Set (Model m))))]
  apply (Theory.GroupTheory.primeRank_le_of_injective p
    (inclusion hg) (inclusion_injective hg)).trans
  cases s with
  | suzuki => exact suzuki_primeRank_le_two_of_projection hm πs hπs hp ho
  | linear => exact linear_primeRank_le_two_of_projection πl hπl hp ho

/-- Coverage and the actual root radicals promote maximal two-local
containment to equality with a conjugate full parabolic. -/
public theorem maximalTwoLocal_eq_parabolic_of_cover {m : ℕ}
    (hcover : ∀ R : Subgroup (Model m), R ≠ ⊥ → IsPGroup 2 R →
      ∃ (g : Model m) (s : Side),
        (normalizer (R : Set (Model m))).map (MulAut.conj g).toMonoidHom ≤ parabolic m s)
    (hne : ∀ s : Side, radical m s ≠ ⊥)
    (hnorm : ∀ s : Side,
      parabolic m s ≤ normalizer (radical m s : Set (Model m)))
    {M : Subgroup (Model m)} (hM : IsMaximalTwoLocal M) :
    ∃ (g : Model m) (s : Side), M.map (MulAut.conj g).toMonoidHom = parabolic m s := by
  obtain ⟨R, hR, hpR, hMR⟩ := hM.1
  obtain ⟨g, s, hg⟩ := hcover R hR hpR
  rw [← hMR] at hg
  have hmap := Theory.GroupTheory.isMaximalTwoLocal_map (MulAut.conj g) hM
  have hN : IsTwoLocal (normalizer (radical m s : Set (Model m))) :=
    ⟨radical m s, hne s, radical_isPGroup m s, rfl⟩
  exact ⟨g, s, le_antisymm hg ((hnorm s).trans (hmap.2 hN (hg.trans (hnorm s))))⟩

/-- The centralizer is calculated inside the full parabolic and then
transported with its intrinsic two-core. This proves E for every Sylow. -/
public theorem evenCharacteristic_of_radical_calculations {m : ℕ}
    (hcover : ∀ R : Subgroup (Model m), R ≠ ⊥ → IsPGroup 2 R →
      ∃ (g : Model m) (s : Side),
        (normalizer (R : Set (Model m))).map (MulAut.conj g).toMonoidHom ≤ parabolic m s)
    (hne : ∀ s : Side, radical m s ≠ ⊥)
    (hnorm : ∀ s : Side,
      parabolic m s ≤ normalizer (radical m s : Set (Model m)))
    (hc : ∀ s : Side,
      centralizer (intrinsicRadical m s : Set (parabolic m s)) ≤ intrinsicRadical m s) :
    IsEvenCharacteristic (Model m) := by
  intro T M hM _
  obtain ⟨g, s, hP⟩ := maximalTwoLocal_eq_parabolic_of_cover hcover hne hnorm hM
  apply (Theory.Quasithin.centralizer_pCore_map_le_iff 2 (MulAut.conj g) M).mp
  rw [hP]
  exact centralizer_pCore_le_of_radical (hnorm s) (hc s)

/-- Conditional assembly along an actual Ree model equivalence. The root
projections, coverage, and radical calculations must still be constructed. -/
public theorem quasithin_evenCharacteristic_of_root_calculations_of_iso
    {G : Type*} [Group G] [Finite G] {m : ℕ} (hm : 1 ≤ m) (e : G ≃* Model m)
    (hcover : ∀ R : Subgroup (Model m), R ≠ ⊥ → IsPGroup 2 R →
      ∃ (g : Model m) (s : Side),
        (normalizer (R : Set (Model m))).map (MulAut.conj g).toMonoidHom ≤ parabolic m s)
    (πs : parabolic m .suzuki →* SuzukiMatrixGroup m × (CoefficientField m)ˣ)
    (hπs : IsPGroup 2 πs.ker)
    (πl : parabolic m .linear →*
      Matrix.SpecialLinearGroup (Fin 2) (CoefficientField m) × (CoefficientField m)ˣ)
    (hπl : IsPGroup 2 πl.ker)
    (hne : ∀ s : Side, radical m s ≠ ⊥)
    (hnorm : ∀ s : Side,
      parabolic m s ≤ normalizer (radical m s : Set (Model m)))
    (hc : ∀ s : Side,
      centralizer (intrinsicRadical m s : Set (parabolic m s)) ≤ intrinsicRadical m s) :
    IsQuasithin G ∧ IsEvenCharacteristic G :=
  ⟨Theory.GroupTheory.isQuasithin_of_equiv e.symm
      (quasithin_of_root_projections hm hcover πs hπs πl hπl),
    evenCharacteristic_of_model_equiv e
      (evenCharacteristic_of_radical_calculations hcover hne hnorm hc)⟩

private theorem radical_ne_bot {m : ℕ} (hm : 1 ≤ m) (s : Side) :
    radical m s ≠ ⊥ := by
  cases s with
  | suzuki => exact suzuki_radical_ne_bot m
  | linear => exact linear_radical_ne_bot hm

private theorem parabolic_le_radical_normalizer (m : ℕ) (s : Side) :
    parabolic m s ≤ normalizer (radical m s : Set (Model m)) := by
  cases s with
  | suzuki => exact suzuki_parabolic_le_radical_normalizer m
  | linear => exact linear_parabolic_le_radical_normalizer m

private theorem intrinsicRadical_centralizer_le {m : ℕ} (hm : 1 ≤ m) (s : Side) :
    centralizer (intrinsicRadical m s : Set (parabolic m s)) ≤ intrinsicRadical m s := by
  cases s with
  | suzuki => exact suzuki_intrinsicRadical_centralizer_le hm
  | linear => exact linear_intrinsicRadical_centralizer_le hm

/-- Every two-local of the genuine Ree group has odd-prime ranks at most two.
The full-parabolic projections and normalizer coverage are all discharged. -/
public theorem model_quasithin {m : ℕ} (hm : 1 ≤ m) : IsQuasithin (Model m) :=
  quasithin_of_root_projections hm (normalizer_cover hm)
    (suzukiProjection hm) (suzukiProjection_ker_isPGroup hm)
    (linearProjection hm) (linearProjection_ker_isPGroup hm)

/-- Every maximal two-local has self-centralizing intrinsic two-core,
by conjugacy to a full parabolic and relative normality of its root radical. -/
public theorem model_maximalTwoLocal_characteristicTwo {m : ℕ} (hm : 1 ≤ m)
    {M : Subgroup (Model m)} (hM : IsMaximalTwoLocal M) : HasCharacteristicTwo M := by
  obtain ⟨g, s, hP⟩ := maximalTwoLocal_eq_parabolic_of_cover (normalizer_cover hm)
    (radical_ne_bot hm) (parabolic_le_radical_normalizer m) hM
  apply (Theory.Quasithin.centralizer_pCore_map_le_iff 2 (MulAut.conj g) M).mp
  rw [hP]
  exact centralizer_pCore_le_of_radical (parabolic_le_radical_normalizer m s)
    (intrinsicRadical_centralizer_le hm s)

/-- Condition E for the genuine Ree carrier, for every Sylow two-subgroup. -/
public theorem model_evenCharacteristic {m : ℕ} (hm : 1 ≤ m) :
    IsEvenCharacteristic (Model m) :=
  fun _ _ hM _ => model_maximalTwoLocal_characteristicTwo hm hM

/-- The QT and E clauses of the general Ree case of Theorem 0.1.2(1),
transported along an actual isomorphism to the exceptional fixed subgroup. -/
public theorem quasithin_evenCharacteristic_of_iso
    {G : Type*} [Group G] [Finite G] {m : ℕ} (hm : 1 ≤ m) (e : G ≃* Model m) :
    IsQuasithin G ∧ IsEvenCharacteristic G :=
  ⟨Theory.GroupTheory.isQuasithin_of_equiv e.symm (model_quasithin hm),
    evenCharacteristic_of_model_equiv e (model_evenCharacteristic hm)⟩

/-- The actual Ree family witness supplies both local clauses. Its parameter
restriction excludes the full nonsimple ²F₄(2) and the separate Tits endpoint. -/
public theorem quasithin_evenCharacteristic {G : Type*} [Group G] [Finite G]
    (hG : IsReeF4Model G) : IsQuasithin G ∧ IsEvenCharacteristic G := by
  obtain ⟨m, hm, ⟨e⟩⟩ := hG
  exact quasithin_evenCharacteristic_of_iso hm e

/-- The Ree converse on the proper-K induction domain. The class parameter
can be instantiated with the complete known-simple catalogue by the main theorem. -/
public theorem isQTKE_of_properK {G : Type*} [Group G] [Finite G] {K : GroupClass}
    (hK : HasProperKSubgroups K G) (hG : IsReeF4Model G) : IsQTKE K G := by
  obtain ⟨hQT, hE⟩ := quasithin_evenCharacteristic hG
  exact ⟨hQT, hK, hE⟩

end CFSG.Quasithin.MainConverse.ReeLocal
