module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CoreOrbits
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.DihedralCoreGeneration
public import BenderSuzuki.Converse.PSU3
public import Theory.GroupTheory.SylowNormalizerCentralQuotient

/-!
# All beta rows of the Chapter 11 core identities for linear alpha

The actual Hermitian root action is regular away from its distinguished
isotropic point at every positive binary field degree. Sylow conjugacy
transports this orbit to every Sylow normalizer. A Hermitian basis change
retains the original field and form; the central SU₃-to-PSU₃ projection
pulls back precisely the Sylow normalizer, so both quotient markings give
the same required neighbor orbit without identifying their groups.

The order-twenty Suzuki endpoint is handled on its actual five-point ovoid.
Combining these orbits with CoreOrbits proves the opposite-seed supplement
and pair-core identity for the nonlinear beta rows. The final theorem covers
every constructor of the earlier local quotient catalogue, including all
small parameters and D₁₀, whenever alpha has an actual linear marking.

Selecting that alpha row, the full center orders and module structures of
(11.7)--(11.8), the exclusions, general path profile and marked assembly remain
source obligations. No classification result or full-kernel/core equality
is assumed. Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs
(1985), (11.3)(h)--(11.5), pp.169--172; Huppert II.10.12 and
Huppert--Blackburn III, XI.3.3 for the model root actions.
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups LinearAlgebra.Projectivization
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open BenderSuzuki.MatrixGroups BenderSuzuki.External

private theorem all_sylow_orbits {D X : Type*} [Group D] [Finite D] [MulAction D X]
    (S : Sylow 2 D) (p : X) (hN : normalizer (S : Set D) = MulAction.stabilizer D p)
    (ht : ∀ x y : X, x ≠ p → y ≠ p → ∃ t ∈ (S : Subgroup D), t • x = y)
    (R : Sylow 2 D) :
    ∃ p : X, normalizer (R : Set D) = MulAction.stabilizer D p ∧
      ∀ x y : X, x ≠ p → y ≠ p → ∃ t ∈ (R : Subgroup D), t • x = y := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq D S R
  have hm : (S : Subgroup D).map (MulAut.conj g).toMonoidHom = R := by
    rw [←hg,Sylow.coe_subgroup_smul,Subgroup.pointwise_smul_def]
    rfl
  refine ⟨g • p,?_,?_⟩
  · have he := Subgroup.map_equiv_normalizer_eq (S : Subgroup D) (MulAut.conj g)
    rw [hm] at he
    simp only [Sylow.coe_coe] at he
    rw [hN] at he
    rw [←he,MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  · intro x y hx hy
    obtain ⟨t,htS,hte⟩ := ht (g⁻¹ • x) (g⁻¹ • y)
      (fun he => hx (by rw [←he,smul_inv_smul]))
      (fun he => hy (by rw [←he,smul_inv_smul]))
    refine ⟨g*t*g⁻¹,?_,?_⟩
    · rw [←hm]
      exact mem_map_of_mem (MulAut.conj g).toMonoidHom htS
    · rw [mul_smul,mul_smul,hte,smul_inv_smul]

private theorem orbit_action_pullback {C D X : Type*} [Group C] [Finite C] [Group D]
    (f : C →* D) (hf : Function.Surjective f) (hk : f.ker ≤ center C)
    [MulAction D X]
    (ho : ∀ R : Sylow 2 D, ∃ p : X,
      normalizer (R : Set D) = MulAction.stabilizer D p ∧
      ∀ x y : X, x ≠ p → y ≠ p → ∃ t ∈ (R : Subgroup D), t • x = y) :
    letI : MulAction C X := MulAction.compHom X f
    ∀ R : Sylow 2 C, ∃ p : X,
      normalizer (R : Set C) = MulAction.stabilizer C p ∧
      ∀ x y : X, x ≠ p → y ≠ p → ∃ t ∈ (R : Subgroup C), t • x = y := by
  let : MulAction C X := MulAction.compHom X f
  intro R
  obtain ⟨p,hp,ht⟩ := ho (R.mapSurjective hf)
  refine ⟨p,?_,?_⟩
  · have he := R.normalizer_comap_of_central_kernel f hf hk
    rw [hp] at he
    exact he.symm
  · intro x y hx hy
    obtain ⟨_,⟨t,htR,rfl⟩,he⟩ := ht x y hx hy
    exact ⟨t,htR,he⟩

private instance {E : Type*} [Field E] [Finite E] :
    Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

private theorem unitary_root_orbit {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 0 < n) (hc : Nat.card E = (2^n)^2)
    (hf : Nat.card {x : E // J.conj x = x} = 2^n) :
    ∃ (act : MulAction (ProjectiveSpecialUnitaryMatrixGroup J) (BenderSuzuki.Converse.psuOmega J)),
      letI := act
      ∀ R : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
        ∃ p : BenderSuzuki.Converse.psuOmega J,
          normalizer (R : Set (ProjectiveSpecialUnitaryMatrixGroup J)) =
            MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) p ∧
          ∀ x y : BenderSuzuki.Converse.psuOmega J, x ≠ p → y ≠ p →
            ∃ t ∈ (R : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)), t • x = y := by
  obtain ⟨_,ρ,o,_,_,_,hroot,_⟩ := huppert_II_10_12 J (2^n) hc hf hJ
  obtain ⟨R,D,hRle,_,hnR,_,_,_,hcard,_,_,_,hregular,⟨coord,hcoord⟩,_⟩ := hroot
  have hcoord_eq (z : hermitianUnipotentCoord J) :
      (coord z).val = hermitianUnipotentPSU J hJ z := by
    obtain ⟨A,hA,he⟩ := hcoord z
    have hA' : A = hermitianUnipotentGL J z := Units.ext hA
    apply Subtype.ext
    simpa only [hA',hermitianUnipotentPSU_val] using he
  have hR : R = (hermitianUnipotentPSU J hJ).range := by
    apply le_antisymm
    · intro r hr
      obtain ⟨z,hz⟩ := coord.surjective ⟨r,hr⟩
      exact ⟨z,(hcoord_eq z).symm.trans (congrArg Subtype.val hz)⟩
    · rintro r ⟨z,rfl⟩
      rw [←hcoord_eq z]
      exact (coord z).property
  let S := HermitianForm.EvenTwoRank.rootSylow J hJ hn hc hf
  have hSR : (S : Subgroup _) = R := hR.symm
  let act : MulAction (ProjectiveSpecialUnitaryMatrixGroup J) (BenderSuzuki.Converse.psuOmega J) :=
    MulAction.compHom _ ρ
  let := act
  have hne : R ≠ ⊥ := by
    intro he
    have hh : Nat.card R = 1 := he ▸ Subgroup.card_bot
    have hp : 1 < 2^n := one_lt_pow₀ (by decide) (by omega)
    rw [hcard] at hh
    nlinarith [one_lt_pow₀ hp (by decide : (3 : ℕ) ≠ 0)]
  have hN : normalizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J)) =
      MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) o := by
    change normalizer ((S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : Set (ProjectiveSpecialUnitaryMatrixGroup J)) = _
    rw [hSR]
    exact BenderSuzuki.normalizer_eq_stabilizer_of_regular_compl R o hRle hne hregular hnR
  refine ⟨act,all_sylow_orbits S o hN ?_⟩
  intro x y hx hy
  obtain ⟨t,ht,_⟩ := hregular x y hx hy
  exact ⟨t,hSR.symm ▸ t.property,ht⟩

private theorem small_suzuki_orbits (R : Sylow 2 (SuzukiMatrixGroup 0)) :
    ∃ p : SuzukiOvoid 0,
      normalizer (R : Set (SuzukiMatrixGroup 0)) = MulAction.stabilizer (SuzukiMatrixGroup 0) p ∧
      ∀ x y : SuzukiOvoid 0, x ≠ p → y ≠ p →
        ∃ t ∈ (R : Subgroup (SuzukiMatrixGroup 0)), t • x = y := by
  have hcard : Nat.card (SuzukiRootSubgroup 0) = 4 := by
    let K := BenderSuzuki.PFAppendixIII.BinaryGaloisField 1
    let f : K × K → SuzukiRootSubgroup 0 := fun z =>
      ⟨⟨SuzukiRootGL 0 z.1 z.2,
        Subgroup.subset_closure (Or.inl ⟨z.1,z.2,rfl⟩)⟩,
        (mem_suzukiRootSubgroup_iff 0 _).mpr ⟨z.1,z.2,rfl⟩⟩
    have hi : Function.Injective f := by
      intro z w he
      apply Prod.ext
      · have hh := congrArg (fun r : SuzukiRootSubgroup 0 =>
          ((r.val.val : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 1) he
        simpa [f,SuzukiRootGL,SuzukiRootMatrix] using hh
      · have hh := congrArg (fun r : SuzukiRootSubgroup 0 =>
          ((r.val.val : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 2) he
        simpa [f,SuzukiRootGL,SuzukiRootMatrix] using hh
    have hs : Function.Surjective f := by
      intro r
      obtain ⟨a,b,he⟩ := (mem_suzukiRootSubgroup_iff 0 r.val).mp r.property
      exact ⟨(a,b),Subtype.ext (Subtype.ext he.symm)⟩
    have hc : Nat.card K = 2 := GaloisField.card 2 1 (by decide)
    rw [←Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩),Nat.card_prod,hc]

  have hindex : (SuzukiRootSubgroup 0).index = 5 := by
    have hh := (SuzukiRootSubgroup 0).card_mul_index
    rw [hcard,suzukiZero_card] at hh
    omega
  let S : Sylow 2 (SuzukiMatrixGroup 0) :=
    (IsPGroup.of_card (show Nat.card (SuzukiRootSubgroup 0) = 2^2 from hcard)).toSylow
      (by rw [hindex]; decide)
  have hfix : SuzukiRootSubgroup 0 ≤
      MulAction.stabilizer (SuzukiMatrixGroup 0) (suzukiOvoidInfinity 0) := by
    intro g hg
    obtain ⟨a,b,hab⟩ := (mem_suzukiRootSubgroup_iff 0 g).mp hg
    apply Subtype.ext
    rw [suzukiOvoid_smul_val]
    change (Matrix.GeneralLinearGroup.toLin g.val).toLinearEquiv •
        Projectivization.mk _ ![1,0,0,0] _ = Projectivization.mk _ ![1,0,0,0] _
    rw [hab,Projectivization.smul_mk,Projectivization.mk_eq_mk_iff']
    refine ⟨1,?_⟩
    funext i
    fin_cases i <;> simp [SuzukiRootGL,SuzukiRootMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_four]
  have hstab : MulAction.stabilizer (SuzukiMatrixGroup 0) (suzukiOvoidInfinity 0) =
      SuzukiRootSubgroup 0 := by
    have hh := (MulAction.stabilizer (SuzukiMatrixGroup 0) (suzukiOvoidInfinity 0)).card_mul_index
    rw [MulAction.index_stabilizer_of_transitive,suzukiOvoid_card,suzukiZero_card] at hh
    have hc : Nat.card (MulAction.stabilizer (SuzukiMatrixGroup 0) (suzukiOvoidInfinity 0)) = 4 := by
      change Nat.card (MulAction.stabilizer (SuzukiMatrixGroup 0) (suzukiOvoidInfinity 0)) * 5 = 20 at hh
      omega
    exact (eq_of_le_of_card_ge hfix (by rw [hc,hcard])).symm
  have hN : normalizer (S : Set (SuzukiMatrixGroup 0)) =
      MulAction.stabilizer (SuzukiMatrixGroup 0) (suzukiOvoidInfinity 0) := by
    change normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0)) = _
    have hne : SuzukiRootSubgroup 0 ≠ ⊥ := by
      intro he
      have hh : Nat.card (SuzukiRootSubgroup 0) = 1 := he ▸ Subgroup.card_bot
      omega
    exact BenderSuzuki.normalizer_eq_stabilizer_of_regular_compl
      (SuzukiRootSubgroup 0) _ hfix hne (suzukiRootSubgroup_regular 0)
      (by rw [hstab]; exact le_normalizer)
  apply all_sylow_orbits S _ hN _ R
  intro x y hx hy
  obtain ⟨t,ht,_⟩ := suzukiRootSubgroup_regular 0 x y hx hy
  exact ⟨t,t.property,ht⟩

variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The beta edge radical has its full remaining-neighbor orbit in both
 unitary quotient markings, including fixed field of order two. -/
theorem source_unitary_edge_core_orbit
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c w : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (hbc : (graph (family P)).Adj b c) (hbw : (graph (family P)).Adj b w)
    (hca : c ≠ a) (hwa : w ≠ a)
    {n : ℕ} (hn : 0 < n)
    (hi : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n)) :
    ∃ t ∈ (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2, t • c = w := by
  have M : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)) :=
    hi.elim (.projective_unitary n hn) (.special_unitary n hn)
  rcases hi with hi | hi
  · obtain ⟨E,_,_,J,hc,hf,⟨e⟩⟩ := hi
    have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hc hf
    obtain ⟨f⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
      J (2^n) hc hfixed
    let J₀ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
    obtain ⟨act,ho⟩ := unitary_root_orbit J₀ rfl hn hc hfixed
    let := act
    exact source_edge_core_orbit_of_model_action h hB d hab hbc hbw hca hwa M (e.trans f) ho
  · obtain ⟨E,_,_,J,hc,hf,⟨e⟩⟩ := hi
    have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hc hf
    obtain ⟨f⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
      J (2^n) hc hfixed
    let J₀ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
    obtain ⟨act,ho⟩ := unitary_root_orbit J₀ rfl hn hc hfixed
    let := act
    let π := f.toMonoidHom.comp J.specialToProjective
    have hπ : Function.Surjective π := f.surjective.comp J.specialToProjective_surjective
    have hk : π.ker ≤ center J.specialSubgroup := by
      have he : π.ker = J.specialToProjective.ker := by
        ext x
        change f (J.specialToProjective x) = 1 ↔ J.specialToProjective x = 1
        exact map_eq_one_iff f f.injective
      rw [he]
      exact J.specialToProjective_ker_le_center
    have hOrbit := orbit_action_pullback π hπ hk ho
    let : MulAction J.specialSubgroup (BenderSuzuki.Converse.psuOmega J₀) := MulAction.compHom _ π
    exact source_edge_core_orbit_of_model_action h hB d hab hbc hbw hca hwa M e hOrbit

variable {k : Type*} [Field k] [Finite k] [CharP k 2]

/-- A linear alpha and either literal unitary beta marking supply both
 core identities. No rank-one field is replaced by a family label. -/
theorem source_linear_unitary_core_identities (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    {n : ℕ} (hn : 0 < n)
    (hi : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n)) :
    (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
        Q (family P) a ⊔ Q (family P) b ∧
      Q (family P) b = pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) ⊔
        (Q (family P) a ⊓ Q (family P) b) := by
  have Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)) :=
    hi.elim (.projective_unitary n hn) (.special_unitary n hn)
  have hab := source_critical_one_adjacent hc hb
  have hsupp := source_seed_supplement_of_edge_orbit h hab hbc
    (source_linear_betaSpan_supplement h hB d hc hb hbc hac Ma Mb ea)
    (fun w hw hwa => source_unitary_edge_core_orbit h hB d hab hbc hw hac.symm hwa hn hi)
  exact ⟨source_linear_edge_core_product h hB d hc hb hbc hac Ma Mb ea,
    source_pair_core_of_seed_supplement h hab hsupp⟩

private theorem linear_coordinates {H : Type*} [Group H] {n : ℕ}
    (hM : ClassicalGroup.IsPSL H 2 (2 ^ n)) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2), Nonempty (H ≃* SL(2,k)) := by
  obtain ⟨k,hk,hfin,hcard,⟨e⟩⟩ := hM
  let := Fintype.ofFinite k
  let : CharP k 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let f : SL(2,k) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  exact ⟨k,hk,hfin,inferInstance,⟨e.trans f.symm⟩⟩

/-- Source (11.3)(h) and (11.4) for a linear alpha and every beta constructor
 of the actual earlier catalogue, including Sz(2), SU₃(2), PSU₃(2) and D₁₀. -/
theorem source_linear_rankOne_core_identities (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k)) :
    (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
        Q (family P) a ⊔ Q (family P) b ∧
      Q (family P) b = pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) ⊔
        (Q (family P) a ⊓ Q (family P) b) := by
  refine ⟨source_linear_edge_core_product h hB d hc hb hbc hac Ma Mb ea,?_⟩
  cases Mb with
  | linear m hm hi =>
    obtain ⟨k',hk',hfin',hchar',⟨eb⟩⟩ := linear_coordinates hi
    exact source_linear_pair_core_generation h hB d hc hb hbc hac Ma (.linear m hm hi) ea eb
  | suzuki m hi =>
    obtain ⟨eb⟩ := hi
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have hab := source_critical_one_adjacent hc hb
      have hsupp := source_seed_supplement_of_edge_orbit h hab hbc
        (source_linear_betaSpan_supplement h hB d hc hb hbc hac Ma (.suzuki 0 ⟨eb⟩) ea)
        (fun w hw hwa => source_edge_core_orbit_of_model_action h hB d hab hbc hw
          hac.symm hwa (.suzuki 0 ⟨eb⟩) eb small_suzuki_orbits)
      exact source_pair_core_of_seed_supplement h hab hsupp
    · exact (source_linear_suzuki_core_identities h hB d hc hb hbc hac Ma ea hm eb).2
  | projective_unitary n hn hi =>
    exact (source_linear_unitary_core_identities h hB d hc hb hbc hac Ma ea hn (.inl hi)).2
  | special_unitary n hn hi =>
    exact (source_linear_unitary_core_identities h hB d hc hb hbc hac Ma ea hn (.inr hi)).2
  | dihedral hi =>
    exact source_linear_dihedral_pair_core_generation h hB d hc hb hbc hac Ma ea hi.some

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
