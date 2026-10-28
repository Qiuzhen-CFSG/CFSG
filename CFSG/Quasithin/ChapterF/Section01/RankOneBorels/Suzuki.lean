module

public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.QuotientGeometry
public import Theory.SpecificGroups.Suzuki.RootOvoidGeometry
public import BenderSuzuki.External.Huppert.XI.theorem_3_6
public import BenderSuzuki.MatrixGroups.SuzukiZero

/-!
# Concrete Suzuki Borels for F.1.3(1)

For every parameter, the normalizer of the standard root group is the
root–torus Borel. All Sylow two-subgroups inherit its properness, unique
proper-overgroup property, solvability and abelian odd-order complement.

For positive parameters, a subgroup containing the root group and moving
infinity is transitive on the ovoid. Since the infinity stabilizer normalizes
the root group, such a subgroup contains every conjugate of the root group.
Simplicity therefore makes it the whole group. For parameter zero, the root
group has prime index five, so every proper overgroup equals the root group.
Root regularity proves properness of its normalizer, including at zero.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed
pp.259–260, F.1.3(1), and the Cartan observation in its proof. The concrete
ovoid and simplicity inputs are Huppert–Blackburn III, XI.3.3 and XI.3.6.
-/

open BenderSuzuki BenderSuzuki.MatrixGroups
open scoped Pointwise LinearAlgebra.Projectivization
namespace CFSG.Quasithin.ChapterF.Source

private theorem root_card (m : ℕ) :
    Nat.card (SuzukiRootSubgroup m) = (2 ^ (2 * m + 1)) ^ 2 := by
  let K := PFAppendixIII.BinaryGaloisField (2 * m + 1)
  let f : K × K → SuzukiRootSubgroup m := fun z =>
    ⟨⟨SuzukiRootGL m z.1 z.2,
      Subgroup.subset_closure (Or.inl ⟨z.1, z.2, rfl⟩)⟩,
      (mem_suzukiRootSubgroup_iff m _).mpr ⟨z.1, z.2, rfl⟩⟩
  have hi : Function.Injective f := by
    intro z w h
    apply Prod.ext
    · have h01 := congrArg (fun r : SuzukiRootSubgroup m =>
        ((r.val.val : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 1) h
      simpa [f, SuzukiRootGL, SuzukiRootMatrix] using h01
    · have h02 := congrArg (fun r : SuzukiRootSubgroup m =>
        ((r.val.val : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 2) h
      simpa [f, SuzukiRootGL, SuzukiRootMatrix] using h02
  have hs : Function.Surjective f := by
    intro r
    obtain ⟨a, b, hab⟩ := (mem_suzukiRootSubgroup_iff m r.val).mp r.property
    exact ⟨(a, b), Subtype.ext (Subtype.ext hab.symm)⟩
  have hK : Nat.card K = 2 ^ (2 * m + 1) :=
    GaloisField.card 2 (2 * m + 1) (by omega)
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hi, hs⟩), Nat.card_prod, hK, pow_two]

private theorem root_fix (m : ℕ) (g : SuzukiMatrixGroup m)
    (hg : g ∈ SuzukiRootSubgroup m) :
    g • suzukiOvoidInfinity m = suzukiOvoidInfinity m := by
  obtain ⟨a, b, hab⟩ := (mem_suzukiRootSubgroup_iff m g).mp hg
  apply Subtype.ext
  rw [suzukiOvoid_smul_val]
  change (Matrix.GeneralLinearGroup.toLin g.val).toLinearEquiv •
      Projectivization.mk _ ![1, 0, 0, 0] _ =
      Projectivization.mk _ ![1, 0, 0, 0] _
  rw [hab, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨1, ?_⟩
  funext i
  fin_cases i <;>
    simp [SuzukiRootGL, SuzukiRootMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four]

private theorem root_fixed_iff (m : ℕ) (g : SuzukiMatrixGroup m)
    (hg : g ∈ SuzukiRootSubgroup m) (hne : g ≠ 1) (a : SuzukiOvoid m) :
    g • a = a ↔ a = suzukiOvoidInfinity m := by
  constructor
  · intro hf
    by_contra ha
    obtain ⟨r, _, hu⟩ := suzukiRootSubgroup_regular m a a ha ha
    have he : (⟨g, hg⟩ : SuzukiRootSubgroup m) = 1 :=
      (hu ⟨g, hg⟩ hf).trans (hu 1 (one_smul _ a)).symm
    exact hne (congrArg Subtype.val he)
  · rintro rfl
    exact root_fix m g hg

private theorem root_normalizer_le_stabilizer (m : ℕ) :
    Subgroup.normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)) ≤
      MulAction.stabilizer (SuzukiMatrixGroup m) (suzukiOvoidInfinity m) := by
  intro g hg
  have : Nontrivial (SuzukiRootSubgroup m) := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    rw [root_card]
    have hq : 1 < 2 ^ (2 * m + 1) := one_lt_pow₀ (by decide) (by omega)
    nlinarith
  obtain ⟨r, hr⟩ := exists_ne (1 : SuzukiRootSubgroup m)
  have hrne : (r : SuzukiMatrixGroup m) ≠ 1 := fun h => hr (Subtype.ext h)
  have hmem : g⁻¹ * (r : SuzukiMatrixGroup m) * g ∈ SuzukiRootSubgroup m :=
    (Subgroup.mem_normalizer_iff''.mp hg (r : SuzukiMatrixGroup m)).mp r.property
  have hfix : (r : SuzukiMatrixGroup m) • (g • suzukiOvoidInfinity m) =
      g • suzukiOvoidInfinity m := by
    have h := congrArg (g • ·) (root_fix m _ hmem)
    simpa only [mul_smul, smul_inv_smul] using h
  exact (root_fixed_iff m r r.property hrne _).mp hfix

private theorem root_normalizer_proper (m : ℕ) :
    Subgroup.normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)) < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro he
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m)
    (suzukiOvoidInfinity m) (suzukiOvoidZero m)
  have hf := root_normalizer_le_stabilizer m (he ▸ (Subgroup.mem_top g))
  exact suzukiOvoidInfinity_ne_zero m (hf.symm.trans hg)

private theorem zero_root_index : (SuzukiRootSubgroup 0).index = 5 := by
  have h := (SuzukiRootSubgroup 0).card_mul_index
  rw [root_card, suzukiZero_card] at h
  norm_num at h ⊢
  omega

private theorem zero_overgroup (M : Subgroup (SuzukiMatrixGroup 0))
    (hRM : SuzukiRootSubgroup 0 ≤ M) (hM : M < ⊤) :
    M ≤ SuzukiRootSubgroup 0 := by
  have hd : M.index ∣ 5 := by
    rw [← zero_root_index]
    exact Subgroup.index_dvd_of_le hRM
  have hi : M.index = 5 := ((Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd).resolve_left
    (fun h => hM.ne (Subgroup.index_eq_one.mp h))
  have h := Subgroup.relIndex_mul_index hRM
  rw [zero_root_index, hi] at h
  exact Subgroup.relIndex_eq_one.mp (by omega)

private theorem zero_normalizer :
    Subgroup.normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0)) = SuzukiRootSubgroup 0 :=
  le_antisymm (zero_overgroup _ Subgroup.le_normalizer (root_normalizer_proper 0))
    Subgroup.le_normalizer

private theorem root_unique (m : ℕ) (hm : 0 < m)
    (M : Subgroup (SuzukiMatrixGroup m)) (hRM : SuzukiRootSubgroup m ≤ M)
    (hM : M < ⊤) : M ≤ Subgroup.normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)) := by
  let : IsSimpleGroup (SuzukiMatrixGroup m) := (External.huppert_blackburn_XI_3_6 m hm).1
  by_contra hn
  obtain ⟨g, hg, hgn⟩ := Set.not_subset.mp hn
  have hmove : g • suzukiOvoidInfinity m ≠ suzukiOvoidInfinity m := by
    change g ∉ Subgroup.normalizer (SuzukiRootSubgroup m : Set _) at hgn
    simpa only [suzukiRootSubgroup_normalizer m hm,
      suzukiBorelSubgroup_eq_stabilizer m hm, MulAction.mem_stabilizer_iff] using hgn
  have htrans (a : SuzukiOvoid m) : ∃ k : M,
      (k : SuzukiMatrixGroup m) • suzukiOvoidInfinity m = a := by
    by_cases ha : a = suzukiOvoidInfinity m
    · exact ⟨1, by simp [ha]⟩
    obtain ⟨r, hr, _⟩ := suzukiRootSubgroup_regular m _ a hmove ha
    exact ⟨⟨(r : SuzukiMatrixGroup m) * g, M.mul_mem (hRM r.property) hg⟩,
      by simpa only [mul_smul] using hr⟩
  have hcl : Subgroup.normalClosure (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)) ≤ M := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro x hx
    obtain ⟨r, hr, hc⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp hc
    obtain ⟨k, hk⟩ := htrans (c • suzukiOvoidInfinity m)
    have hck : (k : SuzukiMatrixGroup m)⁻¹ * c ∈
        Subgroup.normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)) := by
      rw [suzukiRootSubgroup_normalizer m hm, suzukiBorelSubgroup_eq_stabilizer m hm,
        MulAction.mem_stabilizer_iff, mul_smul, ← hk, inv_smul_smul]
    have hr' := (Subgroup.mem_normalizer_iff.mp hck r).mp hr
    have h := M.mul_mem (M.mul_mem k.property (hRM hr')) (M.inv_mem k.property)
    convert h using 1
    simp [mul_assoc]
  have he : Subgroup.normalClosure (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)) = ⊤ := by
    apply Subgroup.normalClosure_normal.eq_bot_or_eq_top.resolve_left
    intro hb
    have hb' : SuzukiRootSubgroup m = ⊥ :=
      le_bot_iff.mp (hb ▸ Subgroup.le_normalClosure)
    have hc := root_card m
    have hc' : Nat.card (SuzukiRootSubgroup m) = 1 := by rw [hb']; simp
    rw [hc'] at hc
    have hq : 1 < 2 ^ (2 * m + 1) := one_lt_pow₀ (by decide) (by omega)
    nlinarith
  exact hM.ne (top_unique (he ▸ hcl))


/-- The concrete root normalizer is the root–torus Borel, including `Sz(2)`. -/
public theorem suzuki_root_normalizer_eq_borel (m : ℕ) :
    Subgroup.normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)) =
      SuzukiBorelSubgroup m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [zero_normalizer, suzukiBorelSubgroup_eq_sup]
    apply (sup_eq_left.mpr ?_).symm
    exact (suzukiSplitTorus_le_normalizer_root 0).trans zero_normalizer.le
  · exact suzukiRootSubgroup_normalizer m hm

private theorem root_isSylow (m : ℕ) :
    ∃ P : Sylow 2 (SuzukiMatrixGroup m),
      (P : Subgroup (SuzukiMatrixGroup m)) = SuzukiRootSubgroup m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hp : IsPGroup 2 (SuzukiRootSubgroup 0) := by
      apply IsPGroup.of_card_dvd_pow (n := 2)
      rw [root_card]
      norm_num
    exact ⟨hp.toSylow (by rw [zero_root_index]; decide), rfl⟩
  · exact suzukiRootSubgroup_isSylow m hm

private theorem root_facts (m : ℕ) (P : Sylow 2 (SuzukiMatrixGroup m))
    (hP : (P : Subgroup (SuzukiMatrixGroup m)) = SuzukiRootSubgroup m) :
    RankOneSylowFacts P := by
  refine ⟨?_, ?_, twoCore_sylow_normalizer P, ?_, ?_⟩
  · change Subgroup.normalizer ((P : Subgroup (SuzukiMatrixGroup m)) : Set (SuzukiMatrixGroup m)) < ⊤
    rw [hP]
    exact root_normalizer_proper m
  · intro M hPM hM
    change M ≤ Subgroup.normalizer ((P : Subgroup (SuzukiMatrixGroup m)) : Set (SuzukiMatrixGroup m))
    rw [hP] at hPM ⊢
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact (zero_overgroup M hPM hM).trans Subgroup.le_normalizer
    · exact root_unique m hm M hPM hM
  · change Group.IsSolvable (Subgroup.normalizer ((P : Subgroup (SuzukiMatrixGroup m)) : Set (SuzukiMatrixGroup m)))
    rw [hP]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · let := suzukiZero_isSolvable
      infer_instance
    · rw [suzukiRootSubgroup_normalizer m hm]
      exact suzukiBorelSubgroup_isSolvable m hm
  · change ∃ D : Subgroup (SuzukiMatrixGroup m),
      D ≤ Subgroup.normalizer ((P : Subgroup (SuzukiMatrixGroup m)) : Set (SuzukiMatrixGroup m)) ∧
      Nat.Coprime 2 (Nat.card D) ∧ IsMulCommutative D ∧
      Disjoint (P : Subgroup (SuzukiMatrixGroup m)) D ∧
      (P : Subgroup (SuzukiMatrixGroup m)) ⊔ D =
        Subgroup.normalizer ((P : Subgroup (SuzukiMatrixGroup m)) : Set (SuzukiMatrixGroup m))
    rw [hP]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · refine ⟨⊥, bot_le, by simp, inferInstance, disjoint_bot_right, ?_⟩
      simpa using zero_normalizer.symm
    · let : IsCyclic (SuzukiSplitTorus m) := suzukiSplitTorus_isCyclic m hm
      let := IsCyclic.commGroup (α := SuzukiSplitTorus m)
      refine ⟨SuzukiSplitTorus m, suzukiSplitTorus_le_normalizer_root m, ?_,
        inferInstance, suzukiRootSubgroup_disjoint_splitTorus m hm, ?_⟩
      · rw [suzukiSplitTorus_card m hm]
        exact (Nat.Even.sub_odd (by positivity : 0 < 2 ^ (2 * m + 1))
          (even_two.pow_of_ne_zero (by omega)) odd_one).coprime_two_left
      · rw [suzukiRootSubgroup_normalizer m hm, suzukiBorelSubgroup_eq_sup]

private theorem facts_transport {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (P : Sylow 2 G) (T : Sylow 2 H)
    (hT : (P : Subgroup G).map e.toMonoidHom = (T : Subgroup H))
    (h : RankOneSylowFacts P) : RankOneSylowFacts T := by
  have hn : (Subgroup.normalizer (P : Set G)).map e.toMonoidHom =
      Subgroup.normalizer (T : Set H) := by
    change (Subgroup.normalizer ((P : Subgroup G) : Set G)).map e.toMonoidHom =
      Subgroup.normalizer ((T : Subgroup H) : Set H)
    rw [Subgroup.map_normalizer_eq_of_bijective _ e.bijective, hT]
  refine ⟨?_, ?_, twoCore_sylow_normalizer T, ?_, ?_⟩
  · rw [← hn, ← Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
    exact (Subgroup.map_lt_map_iff_of_injective e.injective).mpr h.proper
  · intro M hTM hM
    have hPM : (P : Subgroup G) ≤ M.comap e.toMonoidHom :=
      Subgroup.map_le_iff_le_comap.mp (hT ▸ hTM)
    have hproper : M.comap e.toMonoidHom < ⊤ := by
      apply lt_top_iff_ne_top.mpr
      intro he
      apply hM.ne
      have hh := congrArg (Subgroup.map e.toMonoidHom) he
      simpa only [Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective,
        Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] using hh
    have hh := Subgroup.map_mono (f := e.toMonoidHom) (h.unique_maximal _ hPM hproper)
    simpa only [Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective, hn] using hh
  · rw [← hn]
    let := h.solvable
    let f := (Subgroup.normalizer (P : Set G)).equivMapOfInjective e.toMonoidHom e.injective
    exact Group.isSolvable_of_isSolvable_injective (f := f.symm.toMonoidHom) f.symm.injective
  · obtain ⟨D, hD, hodd, hcomm, hdis, hsup⟩ := h.abelian_odd_complement
    let : IsMulCommutative D := hcomm
    refine ⟨D.map e.toMonoidHom, ?_, ?_, inferInstance, ?_, ?_⟩
    · rw [← hn]
      exact Subgroup.map_mono hD
    · rwa [← Nat.card_congr (D.equivMapOfInjective e.toMonoidHom e.injective).toEquiv]
    · rw [← hT]
      exact Subgroup.disjoint_map e.injective hdis
    · rw [← hT, ← Subgroup.map_sup, hsup, hn]

/-- Every Sylow two-subgroup of every concrete Suzuki group satisfies the
intrinsic conclusions of F.1.3(1), including the degenerate parameter. -/
public theorem suzuki_rankOneSylowFacts (m : ℕ) (T : Sylow 2 (SuzukiMatrixGroup m)) :
    RankOneSylowFacts T := by
  obtain ⟨P, hP⟩ := root_isSylow m
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m) P T
  apply facts_transport (MulAut.conj g) P T _ (root_facts m P hP)
  exact congrArg Sylow.toSubgroup hg

/-- The normalizer of an arbitrary Sylow two-subgroup is an actual conjugate
of the concrete root–torus Borel. -/
public theorem suzuki_sylow_normalizer_eq_conjugate_borel (m : ℕ)
    (T : Sylow 2 (SuzukiMatrixGroup m)) :
    ∃ g : SuzukiMatrixGroup m,
      Subgroup.normalizer (T : Set (SuzukiMatrixGroup m)) =
        (SuzukiBorelSubgroup m).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨P, hP⟩ := root_isSylow m
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m) P T
  have ht : (SuzukiRootSubgroup m).map (MulAut.conj g).toMonoidHom =
      (T : Subgroup (SuzukiMatrixGroup m)) := by
    rw [← hP]
    exact congrArg Sylow.toSubgroup hg
  refine ⟨g, ?_⟩
  rw [← suzuki_root_normalizer_eq_borel,
    Subgroup.map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective, ht]
  rfl

end CFSG.Quasithin.ChapterF.Source
