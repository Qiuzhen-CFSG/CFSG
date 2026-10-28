module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.CoreGrowth.Setup
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.Selection
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.CoreGrowth.Torus.LinearGeometry

/-!
# Transporting the local split torus into the inverted set

Write `C = C_G(u)` and `L = ⟨Z ∩ C⟩`, with the relative convention for `L`
used by `TwoCoreCountingData.linear_centralizer`. The local embedding clause
of `SimpleReduction` makes `M ∩ L` strongly embedded in `L`: the given `z`
lies in the intersection and the given `t` lies in `C` outside `M`.

An odd-order element of `M` inverted by `t` belongs to `D = M ∩ Mᵗ`.
The normal two-complement in `D` puts it in the actual ambient image of
`O_{2'}(D)`. Thus a compatible local torus transports to the precise inverted
set used by the core-growth argument, while retaining containment in `L`.

The final theorem applies the prescribed-involution split-torus construction
in the concrete PSL₂ model. It transfers both the strongly embedded subgroup
and `t` through the supplied model equivalence. The case `q = 2` is proved
separately by the trivial subgroup, so no simplicity assumption at that
parameter is needed.

Source: GLS, Volume 4, Chapter 2, Proposition 17.6 and Sections 3, 16;
Chapter 4, Lemma 3.2(c–e,i), for the linear-model geometry.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

omit [Finite G] in
/-- Inversion places an odd-order element of `M` in the two-point stabilizer;
its normal two-complement then places the element in the odd core. -/
public theorem mem_coreGrowthInvertedSet_of_odd_order
    (h : IsProductDisconnected Z M)
    (hlocal : ∀ Y : Subgroup G, Subgroup.closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y)
    {t : G} (ht : t ∈ Z) (htM : t ∉ M)
    (a : M) (ha : Odd (orderOf a))
    (hinv : t * (a : G) * t⁻¹ = (a : G)⁻¹) :
    a ∈ coreGrowthInvertedSet M t := by
  have htinv := (h.involutions t ht).inv_eq_self
  have haD : (a : G) ∈ residualPairStabilizer M t := by
    refine ⟨a.property, ?_⟩
    apply Subgroup.mem_map.mpr
    refine ⟨(a : G)⁻¹, M.inv_mem a.property, ?_⟩
    change t⁻¹ * (a : G)⁻¹ * (t⁻¹)⁻¹ = (a : G)
    have he := congrArg Inv.inv hinv
    simpa only [mul_inv_rev, inv_inv, htinv, mul_assoc] using he
  obtain ⟨N, hNnormal, hNodd, hquot⟩ :=
    hlocal _ (residualPairStabilizer_localClosure_eq_bot h htM)
  let _ := hNnormal
  have haodd : Nat.Coprime 2 (orderOf (⟨(a : G), haD⟩ : residualPairStabilizer M t)) := by
    simpa using ha.coprime_two_left
  exact ⟨Subgroup.mem_map.mpr ⟨⟨a, haD⟩,
    mem_pPrimeCore_of_normal_complement N hNodd hquot _ haodd, rfl⟩, hinv⟩

omit [Finite G] in
/-- The split-torus order is odd, including the order-one case. -/
public theorem TwoCoreCountingData.sub_one_odd (d : TwoCoreCountingData Z M) :
    Odd (d.q - 1) := by
  obtain ⟨n, hn⟩ := d.binary
  have hn0 : n ≠ 0 := by
    intro he
    simp [he] at hn
    have := d.one_lt
    omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  refine ⟨2 ^ k - 1, ?_⟩
  rw [hn, pow_succ]
  have : 0 < 2 ^ k := pow_pos (by decide) _
  omega

/-- Strong embedding applies to the actual distinguished centralizer closure.
Its proper ambient centralizer and its inside/outside witnesses are derived
from the counting data and the simple reduction. -/
public theorem TwoCoreCountingData.local_stronglyEmbedded
    (d : TwoCoreCountingData Z M) (h : IsProductDisconnected Z M)
    (r : SimpleReduction Z M) :
    IsStronglyEmbedded
      ((M.comap (Subgroup.centralizer ({((d.u : M) : G)} : Set G)).subtype).comap
        (Subgroup.closure
          ((Subgroup.centralizer ({((d.u : M) : G)} : Set G)).subtype ⁻¹' Z)).subtype) := by
  have hu : IsInvolution ((d.u : M) : G) := by
    have ho : orderOf ((d.u : M) : G) = 2 := by simpa using d.u_order
    obtain ⟨hs, hn⟩ := orderOf_eq_prime_iff.mp ho
    exact ⟨hn, hs⟩
  apply r.local_embedding _ (r.involution_centralizer_ne_top h hu)
  · intro hle
    exact d.t_not_mem (hle (Subgroup.mem_centralizer_singleton_iff.mpr d.commutes_t.symm.eq))
  · exact ⟨d.z, d.z_mem,
      Subgroup.mem_centralizer_singleton_iff.mpr d.commutes_z.symm.eq, d.z.property⟩

omit [Finite G] in
/-- Transport a local torus through the actual centralizer inclusion. -/
public theorem TwoCoreCountingData.torus_of_local_subgroup
    (d : TwoCoreCountingData Z M) (h : IsProductDisconnected Z M)
    (hlocal : ∀ Y : Subgroup G, Subgroup.closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y)
    (U : Subgroup (Subgroup.closure
      ((Subgroup.centralizer ({((d.u : M) : G)} : Set G)).subtype ⁻¹' Z)))
    (hUcyc : IsCyclic U) (hUcard : Nat.card U = d.q - 1)
    (hUM : ∀ a ∈ U, ((a : Subgroup.centralizer ({((d.u : M) : G)} : Set G)) : G) ∈ M)
    (hUt : ∀ a ∈ U, d.t * ((a : Subgroup.centralizer ({((d.u : M) : G)} : Set G)) : G) * d.t⁻¹ =
      ((a : Subgroup.centralizer ({((d.u : M) : G)} : Set G)) : G)⁻¹) :
    ∃ A : Subgroup M, IsCyclic A ∧ Nat.card A = d.q - 1 ∧
      (A : Set M) ⊆ coreGrowthInvertedSet M d.t ∧
      A.map M.subtype ≤ centralizerClosure Z ((d.u : M) : G) := by
  let C := Subgroup.centralizer ({((d.u : M) : G)} : Set G)
  let L := Subgroup.closure (C.subtype ⁻¹' Z)
  let f : U →* M := {
    toFun a := ⟨((a : L) : C), hUM a a.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hf : Function.Injective f := by
    intro a b he
    exact Subtype.ext (Subtype.ext (Subtype.ext (congrArg (fun x : M => (x : G)) he)))
  let A := f.range
  let e : U ≃* A := MonoidHom.ofInjective hf
  let _ := hUcyc
  refine ⟨A, isCyclic_of_surjective e e.surjective,
    (Nat.card_congr e.toEquiv).symm.trans hUcard, ?_, ?_⟩
  · rintro a ⟨b, rfl⟩
    apply mem_coreGrowthInvertedSet_of_odd_order h hlocal d.t_mem d.t_not_mem
    · have hdiv : orderOf (f b) ∣ Nat.card U :=
        (orderOf_map_dvd f b).trans (orderOf_dvd_natCard b)
      rw [hUcard] at hdiv
      exact Nat.coprime_two_left.mp (d.sub_one_odd.coprime_two_left.of_dvd_right hdiv)
    · exact hUt b b.property
  · rintro a ⟨b, ⟨c, rfl⟩, rfl⟩
    rw [centralizerClosure_eq_map]
    exact Subgroup.mem_map.mpr ⟨((c : L) : C), (c : L).property, rfl⟩

omit [Finite G] in
/-- At `q = 2` the required torus is trivial; this case needs no local
simple-model geometry or exclusion argument. -/
public theorem TwoCoreCountingData.torus_of_q_eq_two
    (d : TwoCoreCountingData Z M) (hq : d.q = 2) :
    ∃ A : Subgroup M, IsCyclic A ∧ Nat.card A = d.q - 1 ∧
      (A : Set M) ⊆ coreGrowthInvertedSet M d.t ∧
      A.map M.subtype ≤ centralizerClosure Z ((d.u : M) : G) := by
  refine ⟨⊥, inferInstance, ?_, ?_, ?_⟩
  · simp [hq]
  · intro a ha
    rw [Subgroup.mem_bot.mp ha]
    exact one_mem_coreGrowthInvertedSet M d.t
  · simp

/-- Conditional local assembly. The remaining premise is a theorem about the
concrete linear model with a prescribed strongly embedded subgroup and
outside involution; it is not supplied by an unmarked model torus. -/
public theorem TwoCoreCountingData.torus_of_psl2_geometry
    (d : TwoCoreCountingData Z M) (h : IsProductDisconnected Z M)
    (r : SimpleReduction Z M)
    (hlocal : ∀ Y : Subgroup G, Subgroup.closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y)
    (hgeometry : ∀ n : ℕ, 2 ≤ n →
      ∀ B : Subgroup (MatrixGroups.PSL2BinaryMatrixGroup n),
      IsStronglyEmbedded B → ∀ s : MatrixGroups.PSL2BinaryMatrixGroup n,
      IsInvolution s → s ∉ B →
      ∃ U : Subgroup (MatrixGroups.PSL2BinaryMatrixGroup n),
        IsCyclic U ∧ Nat.card U = 2 ^ n - 1 ∧ U ≤ B ∧
        ∀ a ∈ U, s * a * s⁻¹ = a⁻¹) :
    ∃ A : Subgroup M, IsCyclic A ∧ Nat.card A = d.q - 1 ∧
      (A : Set M) ⊆ coreGrowthInvertedSet M d.t ∧
      A.map M.subtype ≤ centralizerClosure Z ((d.u : M) : G) ∧
      A.map M.subtype ≤ Subgroup.centralizer ({((d.u : M) : G)} : Set G) := by
  suffices hh : ∃ A : Subgroup M, IsCyclic A ∧ Nat.card A = d.q - 1 ∧
      (A : Set M) ⊆ coreGrowthInvertedSet M d.t ∧
      A.map M.subtype ≤ centralizerClosure Z ((d.u : M) : G) by
    obtain ⟨A, hc, ho, hi, hl⟩ := hh
    exact ⟨A, hc, ho, hi, hl, hl.trans (centralizerClosure_le _ _)⟩
  by_cases hq : d.q = 2
  · exact d.torus_of_q_eq_two hq
  obtain ⟨n, hn, ⟨e⟩⟩ := d.linear_centralizer
  have hn2 : 2 ≤ n := by
    have hq1 := d.one_lt
    by_contra hn2
    interval_cases n <;> simp_all
  let C := Subgroup.centralizer ({((d.u : M) : G)} : Set G)
  let L := Subgroup.closure (C.subtype ⁻¹' Z)
  let N := (M.comap C.subtype).comap L.subtype
  have hN : IsStronglyEmbedded N := d.local_stronglyEmbedded h r
  let tC : C := ⟨d.t, Subgroup.mem_centralizer_singleton_iff.mpr d.commutes_t.symm.eq⟩
  let s : L := ⟨tC, Subgroup.subset_closure d.t_mem⟩
  have hs : IsInvolution s :=
    IsInvolution.subtype (IsInvolution.subtype (h.involutions d.t d.t_mem) tC.property) s.property
  have hsN : s ∉ N := d.t_not_mem
  let B := N.comap e.symm.toMonoidHom
  have hB : IsStronglyEmbedded B := by
    apply hN.comap_of_injective e.symm.toMonoidHom e.symm.injective
    · intro htop
      apply hN.1
      apply top_unique
      intro a _
      have hm : e a ∈ B := by
        change e a ∈ N.comap e.symm.toMonoidHom
        rw [htop]
        exact Subgroup.mem_top _
      simpa only [B, Subgroup.mem_comap, MulEquiv.toMonoidHom_eq_coe,
        MonoidHom.coe_coe, MulEquiv.symm_apply_apply] using hm
    · obtain ⟨a, ha, hai⟩ := hN.exists_involution
      exact ⟨e a, by simpa only [B, Subgroup.mem_comap, MulEquiv.toMonoidHom_eq_coe,
        MonoidHom.coe_coe, MulEquiv.symm_apply_apply] using ha,
        IsInvolution.map_of_injective hai e.toMonoidHom e.injective⟩
  obtain ⟨V, hVc, hVo, hVB, hVs⟩ := hgeometry n hn2 B hB (e s)
    (IsInvolution.map_of_injective hs e.toMonoidHom e.injective) (by
      simpa only [B, Subgroup.mem_comap, MulEquiv.toMonoidHom_eq_coe,
        MonoidHom.coe_coe, MulEquiv.symm_apply_apply] using hsN)
  let U := V.map e.symm.toMonoidHom
  let eU : V ≃* U := V.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
  apply d.torus_of_local_subgroup h hlocal U
  · exact eU.isCyclic.mp hVc
  · exact (Nat.card_congr eU.toEquiv).symm.trans (hVo.trans (by rw [hn]))
  · rintro a ⟨v, hv, rfl⟩
    exact hVB hv
  · rintro a ⟨v, hv, rfl⟩
    have hh := congrArg e.symm (hVs v hv)
    simp only [map_mul, map_inv, MulEquiv.symm_apply_apply] at hh
    exact congrArg (fun x : L => ((x : C) : G)) hh

/-- The actual local split torus required in Proposition 17.6. It lies in
the distinguished closure in `C_G(u)`, belongs to `M`, and consists of
elements of the ambient image of `O_{2'}(D)` inverted by the given `t`.
Only the normal-complement part of the local hypothesis is needed. -/
public theorem TwoCoreCountingData.exists_local_split_torus
    (d : TwoCoreCountingData Z M) (h : IsProductDisconnected Z M)
    (r : SimpleReduction Z M)
    (hlocal : ∀ Y : Subgroup G, Subgroup.closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y) :
    ∃ A : Subgroup M, IsCyclic A ∧ Nat.card A = d.q - 1 ∧
      (A : Set M) ⊆ coreGrowthInvertedSet M d.t ∧
      A.map M.subtype ≤ centralizerClosure Z ((d.u : M) : G) ∧
      A.map M.subtype ≤ Subgroup.centralizer ({((d.u : M) : G)} : Set G) := by
  apply d.torus_of_psl2_geometry h r hlocal
  intro n hn B hB s hs hsB
  have hcard := Converse.card_binaryGaloisField n (by omega)
  simpa only [hcard] using
    CoreGrowthTorus.psl2_torus_of_stronglyEmbedded hcard B hB s hs hsB

end BenderSuzuki.ZD
