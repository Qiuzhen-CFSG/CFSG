module

public import CFSG.Quasithin.MainConverse.SolvableSections
public import Glauberman.DicksonClassification
public import GorensteinWalter.PGL2DerivedSubgroup
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Theory.SpecificGroups.DihedralSolvable
public import Theory.GroupTheory.SolvableNormalSup
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# Simple sections of finite projective special linear groups of degree two

Dickson's nine-case classification gives every subgroup of the actual PSL₂
matrix group. The elementary abelian, cyclic, dihedral, A₄, S₄ and
abelian-by-cyclic cases are solvable. A simple quotient of A₅ is A₅. A simple
quotient of a subfield PSL₂ is either prime cyclic at field orders two and
three, or isomorphic to that PSL₂. Finally the derived subgroup of PGL₂
lies in the canonical PSL₂ image, so every nonabelian simple quotient of
PGL₂ is already a quotient of PSL₂.

Consequently all simple sections lie in the prime cyclic, alternating-five
or linear part of the concrete catalogue. The proper-K corollary applies
both to PSL₂(2^f), f ≥ 2, and to PSL₂(p) for Fermat or Mersenne primes p ≥ 5;
this clause itself needs no restriction on the finite field order. The
inclusion into the full catalogue is required only for finite simple groups.

Sources: Dickson's theorem in Huppert, *Endliche Gruppen I*, II.8.27;
Aschbacher–Smith, *The Classification of Quasithin Groups*, Main Hypothesis
0.1.1(K) and Theorem 0.1.2, printed p.4 (repeated on p.482). The imported
Dickson proof is intrinsic and does not assume a K-group hypothesis.
-/

namespace CFSG.Quasithin.MainConverse
open CFSG.KnownSimple
open BenderSuzuki.MatrixGroups
open scoped LinearAlgebra.Projectivization

private theorem simple_surjection_equiv {H S : Type*} [Group H] [Group S]
    [IsSimpleGroup H] [Nontrivial S] (f : H →* S) (hf : Function.Surjective f) :
    Nonempty (S ≃* H) := by
  have hinj : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨s, hs⟩ := exists_ne (1 : S)
      obtain ⟨x, rfl⟩ := hf s
      exact hs (show x ∈ f.ker by rw [h]; trivial)
  exact ⟨(MulEquiv.ofBijective f ⟨hinj, hf⟩).symm⟩

private theorem constructed_of_solvable_surjection {H S : Type*} [Group H] [Group S]
    [Group.IsSolvable H] [IsSimpleGroup S] (f : H →* S)
    (hf : Function.Surjective f) : IsConstructedCarrier S := by
  let : Group.IsSolvable S := Group.isSolvable_of_surjective hf
  exact .cyclic (primeCyclic_of_solvable_simple S)

private theorem psl2_solvable_of_card_le_three (F : Type*) [Field F] [Finite F]
    (hF : Nat.card F ≤ 3) : Group.IsSolvable (PSL2MatrixGroup F) := by
  classical
  let Ω := ℙ F (Fin 2 → F)
  let : Fintype Ω := Fintype.ofFinite Ω
  have hΩ : Fintype.card Ω ≤ 4 := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card (ℙ F (Fin 2 → F)) ≤ 4
    rw [Projectivization.card_of_finrank_two F (Fin 2 → F) (by simp)]
    omega
  let i : Ω ↪ Fin 4 :=
    (Fintype.equivFin Ω).toEmbedding.trans (Fin.castLEEmb hΩ)
  let act : PSL2MatrixGroup F →* Equiv.Perm Ω := MulAction.toPermHom _ _
  let a : PSL2MatrixGroup F →* Equiv.Perm (Fin 4) :=
    (Equiv.Perm.viaEmbeddingHom i).comp act
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  exact Group.isSolvable_of_isSolvable_injective (f := a)
    ((Equiv.Perm.viaEmbeddingHom_injective i).comp MulAction.toPerm_injective)

private theorem psl2_simple_quotient_constructed (F : Type) [Field F] [Finite F]
    {S : Type*} [Group S] [IsSimpleGroup S]
    (f : PSL2MatrixGroup F →* S) (hf : Function.Surjective f) :
    IsConstructedCarrier S := by
  by_cases hF : 4 ≤ Nat.card F
  · let : IsSimpleGroup (PSL2MatrixGroup F) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF
    obtain ⟨e⟩ := simple_surjection_equiv f hf
    have hpow : IsPrimePow (Nat.card F) := by
      let : Fintype F := Fintype.ofFinite F
      simpa only [Nat.card_eq_fintype_card] using FiniteField.isPrimePow_card F
    exact .classical (.linear 2 (Nat.card F) ⟨hpow, le_rfl, fun _ => hF⟩
      ⟨F, inferInstance, inferInstance, rfl, ⟨e⟩⟩)
  · let : Group.IsSolvable (PSL2MatrixGroup F) :=
      psl2_solvable_of_card_le_three F (by omega)
    exact constructed_of_solvable_surjection f hf

private theorem pgl2_simple_quotient_constructed (F : Type) [Field F] [Finite F]
    {S : Type*} [Group S] [IsSimpleGroup S]
    (f : Matrix.ProjGenLinGroup (Fin 2) F →* S) (hf : Function.Surjective f) :
    IsConstructedCarrier S := by
  by_cases hs : Group.IsSolvable S
  · let := hs
    exact .cyclic (primeCyclic_of_solvable_simple S)
  have hcomm : commutator S = ⊤ := by
    rcases (inferInstance : (commutator S).Normal).eq_bot_or_eq_top with h | h
    · have hc := (commutator_eq_bot_iff S).mp h
      exact (hs (Group.isSolvable_of_comm hc.is_comm.comm)).elim
    · exact h
  let i : PSL2MatrixGroup F →* Matrix.ProjGenLinGroup (Fin 2) F :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL
  have hrange : (f.comp i).range = ⊤ := by
    apply top_unique
    calc
      ⊤ = commutator S := hcomm.symm
      _ = (commutator (Matrix.ProjGenLinGroup (Fin 2) F)).map f := by
        rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf]
        rfl
      _ ≤ i.range.map f := Subgroup.map_mono (GorensteinWalter.pgl2_commutator_le_psl2_range F)
      _ = (f.comp i).range := (MonoidHom.range_comp f i).symm
  exact psl2_simple_quotient_constructed F (f.comp i)
    (MonoidHom.range_eq_top.mp hrange)

/-- Every simple section of PSL₂ over a finite field is prime cyclic, A₅, or
another concrete PSL₂ model in the simple range. -/
public theorem psl2_simple_section_constructed (F : Type) [Field F] [Finite F]
    {S : Type*} [Group S] [IsSimpleGroup S]
    (U : Subgroup (PSL2MatrixGroup F)) (f : U →* S) (hf : Function.Surjective f) :
    IsConstructedCarrier S := by
  have hpow : IsPrimePow (Nat.card F) := by
    let : Fintype F := Fintype.ofFinite F
    simpa only [Nat.card_eq_fintype_card] using FiniteField.isPrimePow_card F
  obtain ⟨p, n, hp, hn, hcard⟩ := (isPrimePow_nat_iff _).mp hpow
  let : Fact p.Prime := ⟨hp⟩
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification
      hcard.symm U with hEl | hCy | hDi | hA4 | hS4 | hA5 | hSemi | hPSL | hPGL
  · let : IsElementaryAbelian p U := hEl
    let : Group.IsSolvable U := Group.isSolvable_of_comm
      (fun a b => IsMulCommutative.is_comm.comm a b)
    exact constructed_of_solvable_surjection f hf
  · obtain ⟨z, _, _, hcyc⟩ := hCy
    let : IsCyclic U := hcyc
    let : CommGroup U := IsCyclic.commGroup
    exact constructed_of_solvable_surjection f hf
  · obtain ⟨z, _, _, ⟨e⟩⟩ := hDi
    let : Group.IsSolvable (DihedralGroup z) := GLS3.Chapter5.dihedralGroup_isSolvable z
    exact constructed_of_solvable_surjection (f.comp e.symm.toMonoidHom)
      (hf.comp e.symm.surjective)
  · obtain ⟨_, ⟨e⟩⟩ := hA4
    let : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup_fin_four_isSolvable
    exact constructed_of_solvable_surjection (f.comp e.symm.toMonoidHom)
      (hf.comp e.symm.surjective)
  · obtain ⟨_, ⟨e⟩⟩ := hS4
    let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
    exact constructed_of_solvable_surjection (f.comp e.symm.toMonoidHom)
      (hf.comp e.symm.surjective)
  · obtain ⟨_, ⟨e⟩⟩ := hA5
    let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    exact .alternating 5 le_rfl
      (simple_surjection_equiv (f.comp e.symm.toMonoidHom) (hf.comp e.symm.surjective))
  · obtain ⟨m, t, _, _, N, C, hN, hEl, _, hC, _, _, hsup⟩ := hSemi
    let : N.Normal := hN
    let : IsElementaryAbelian p N := hEl
    let : IsCyclic C := hC
    let : Group.IsSolvable N := Group.isSolvable_of_comm
      (fun a b => IsMulCommutative.is_comm.comm a b)
    let : CommGroup C := IsCyclic.commGroup
    let : Group.IsSolvable U := Group.isSolvable_of_normal_sup_eq_top N C hsup
    exact constructed_of_solvable_surjection f hf
  · obtain ⟨m, hm, _, ⟨e⟩⟩ := hPSL
    exact psl2_simple_quotient_constructed (GaloisField p m)
      (f.comp e.symm.toMonoidHom) (hf.comp e.symm.surjective)
  · obtain ⟨m, hm, _, ⟨e⟩⟩ := hPGL
    exact pgl2_simple_quotient_constructed (GaloisField p m)
      (f.comp e.symm.toMonoidHom) (hf.comp e.symm.surjective)

/-- Every group with the exact finite PSL₂ model has only known simple sections. -/
public theorem psl2_isKGroup_constructed {G : Type*} [Group G] {q : ℕ}
    (hmodel : ClassicalGroup.IsPSL G 2 q) : IsKGroup IsConstructedCarrier G := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hmodel
  intro S _ hS U f hf
  let := hS
  let eU := Subgroup.equivMapOfInjective U e.toMonoidHom e.injective
  exact psl2_simple_section_constructed F (U.map e.toMonoidHom)
    (f.comp eU.symm.toMonoidHom) (hf.comp eU.symm.surjective)

/-- Enlarge the explicit linear section list to the full catalogue. This covers
both PSL₂(2^f), f ≥ 2, and PSL₂(p) for Fermat or Mersenne primes p ≥ 5; the
proper-K calculation itself needs no restriction on the finite field order. -/
public theorem psl2_properK_of_catalogue {G : Type*} [Group G]
    {K : GroupClass} {q : ℕ}
    (hK : ∀ (S : Type _) [Group S] [Finite S] [IsSimpleGroup S],
      IsConstructedCarrier S → K S)
    (hmodel : ClassicalGroup.IsPSL G 2 q) : HasProperKSubgroups K G := by
  let : Finite G := hmodel.finite
  apply IsKGroup.properK
  intro S _ hS U f hf
  let := hS
  let : Finite S := Finite.of_surjective f hf
  exact hK S (psl2_isKGroup_constructed hmodel S hS U f hf)

end CFSG.Quasithin.MainConverse
