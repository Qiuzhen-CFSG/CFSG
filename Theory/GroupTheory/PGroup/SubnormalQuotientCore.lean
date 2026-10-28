module
public import Theory.GroupTheory.PGroup.SubnormalCore


/-!
# Subnormal subgroup images in a quotient p-core

Let `K` be subnormal in a finite group `G`. If `K/O_q(K)` is a `p`-group,
then the image of `K` in `G/O_q(G)` lies in the `p`-core of that quotient.
The two prime parameters are explicit; they need not be distinct.

Subnormal monotonicity of the ambient `q`-core puts the image of `O_q(K)`
in `O_q(G)`. Hence the map from `K` to its image in `G/O_q(G)` factors
through `K/O_q(K)`, with a surjective induced map. That image is a
`p`-group and remains subnormal under the quotient map. The established
subnormal `p`-subgroup theorem places it in the quotient's `p`-core.

This standard finite-group transfer supplies the normal odd-prime subgroup
modulo the centralizer two-core in Stellmacher (9.3), Journal of Algebra
190 (1997), p.49. It is independent of the local graph and of the source of
the subnormality or prime-group quotient hypothesis.
-/

/-- A subnormal subgroup with p-group quotient by its q-core maps into the
p-core after quotienting the ambient group by its q-core. -/
public theorem subnormal_map_quotient_core_le_pCore
    {G : Type*} [Group G] [Finite G]
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (K : Subgroup G) (hK : K.IsSubnormal)
    (hquot : IsPGroup p (K ⧸ pCore q K)) :
    K.map (QuotientGroup.mk' (pCore q G)) ≤ pCore p (G ⧸ pCore q G) := by
  let π := QuotientGroup.mk' (pCore q G)
  let I := K.map π
  have hcore : (pCore q K).map K.subtype ≤ pCore q G := by
    have hh := pCoreAmbient_mono_of_isSubnormalIn K ⊤ q le_top
      (hK.comap (⊤ : Subgroup G).subtype)
    have he : (pCore q (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype = pCore q G :=
      pCore_map_iso q Subgroup.topEquiv
    rwa [he] at hh
  let f : K →* I := (π.comp K.subtype).codRestrict I
    (fun k => Subgroup.mem_map_of_mem π k.property)
  have hfker : pCore q K ≤ f.ker := by
    intro k hk
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    change π (k : G) = 1
    exact (QuotientGroup.eq_one_iff _).mpr
      (hcore (Subgroup.mem_map_of_mem K.subtype hk))
  let fbar : K ⧸ pCore q K →* I := QuotientGroup.lift (pCore q K) f hfker
  have hfbar : Function.Surjective fbar := by
    intro y
    obtain ⟨k, hk, he⟩ := y.property
    refine ⟨QuotientGroup.mk' (pCore q K) ⟨k, hk⟩, ?_⟩
    exact Subtype.ext he
  have hIp : IsPGroup p I := hquot.of_surjective fbar hfbar
  have hIsub : I.IsSubnormal := hK.quotient
  have hh := isPGroup_le_pCoreAmbient_of_isSubnormalIn ⊤ I p le_top
    (hIsub.comap (⊤ : Subgroup (G ⧸ pCore q G)).subtype) hIp
  have he : (pCore p (⊤ : Subgroup (G ⧸ pCore q G))).map
      (⊤ : Subgroup (G ⧸ pCore q G)).subtype = pCore p (G ⧸ pCore q G) :=
    pCore_map_iso p Subgroup.topEquiv
  rwa [he] at hh
