module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Contracts
public import Theory.GroupTheory.DihedralHalfOrderClasses
public import Theory.GroupTheory.TwoInvolutionClassOrder.SingletonCommuting

/-!
# Thompson shearing in proper residual centralizers

Every involution `u` of the two-point stabilizer is conjugate to every
member of `C_A(u)u`, where `A = ⟨Z ∩ M⟩`. If shearing fails, displacement
on the elementary abelian subgroup A first forces u to centralize A.
Local punctured-coset conjugacy, transported by an element of M, then
confines the centralizer of each member of `A \ {1}` times u to M.

The dihedral half-order identities and fusion control give one supported
Thompson fiber, consisting of the single pair `(z,u)`. Equivariance of this
fiber forces the two mixed classes to commute elementwise. Distinguished
generation contradicts the nontriviality of u. This is the singleton-fiber
form of the source's Thompson order calculation. The final corollary gives
fusion of all commuting mixed products, as required by the next counts.

All strong embedding used here is inside the proper distinguished
centralizer closure. Neither centralizer collapse nor ambient strong
embedding is assumed. The earlier local-recognition data remain the explicit
input specified by this module's contract.

Source: `refs/KGroup/GLS4/Chapter2.tex`, Definition 12.5 and Lemmas 12.6–12.7,
using Lemmas 12.2, 12.4 and 4.2. The generic singleton-fiber argument is in
`Theory.GroupTheory.TwoInvolutionClassOrder.SingletonCommuting`.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1 TwoInvolutionClassOrder
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
namespace ResidualShearing

omit [Finite G] in
private theorem mem_Z_of_isConj (h : IsProductDisconnected Z M)
    {a b : G} (ha : a ∈ Z) (hab : IsConj a b) : b ∈ Z := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hab
  exact hg ▸ h.invariant g a ha

omit [Finite G] in
private theorem conj_mem_A (h : IsProductDisconnected Z M)
    {m a : G} (hm : m ∈ M) (ha : a ∈ closure (Z ∩ (M : Set G))) :
    MulAut.conj m a ∈ closure (Z ∩ (M : Set G)) := by
  have hmN : m ∈ normalizer (closure (Z ∩ (M : Set G)) : Set G) := by
    rwa [distinguishedClosure_normalizer h]
  exact (mem_normalizer_iff.mp hmN a).mp ha

omit [Finite G] in
private theorem pair_conjugator (ha : ResidualAction Z M)
    {t v : G} (htM : t ∉ M) (hvM : v ∈ M)
    (hC : ¬ centralizer ({v} : Set G) ≤ M) :
    ∃ m ∈ M, MulAut.conj m v ∈ residualPairStabilizer M t := by
  obtain ⟨g, hgC, hgM⟩ := Set.not_subset.mp hC
  let α : G ⧸ M := QuotientGroup.mk 1
  have hstab : MulAction.stabilizer G α = M := MulAction.stabilizer_quotient M
  have hgα : α ≠ g • α := by
    intro he
    exact hgM (hstab ▸ he.symm)
  have htα : α ≠ t⁻¹ • α := by
    intro he
    apply htM
    rw [← hstab]
    exact (inv_smul_eq_iff.mp he.symm).symm
  obtain ⟨m, hmα, hmg⟩ := MulAction.is_two_pretransitive_iff.mp ha.two_transitive hgα htα
  have hvα : v • α = α := MulAction.mem_stabilizer_iff.mp (hstab.symm ▸ hvM)
  have hvg : v • (g • α) = g • α := by
    rw [← mul_smul, ← mem_centralizer_singleton_iff.mp hgC, mul_smul, hvα]
  have hfix (β : G ⧸ M) (hvβ : v • β = β) :
      MulAut.conj m v • (m • β) = m • β := by
    simp only [MulAut.conj_apply, mul_smul, inv_smul_smul, hvβ]
  refine ⟨m, hstab ▸ hmα, ?_, ?_⟩
  · rw [← hstab]
    exact MulAction.mem_stabilizer_iff.mpr (by simpa only [hmα] using hfix α hvα)
  · rw [← hstab, rightConjugate_stabilizer]
    exact MulAction.mem_stabilizer_iff.mpr (by simpa only [hmg] using hfix (g • α) hvg)

private theorem punctured_conjugacy (h : IsProductDisconnected Z M)
    (ha : ResidualAction Z M) {z t v : G}
    (hlocal : ResidualCentralizerLocalData Z M z t) (htM : t ∉ M)
    (hv : PFAppendixIII.IsInvolution v) (hvM : v ∈ M)
    (hC : ¬ centralizer ({v} : Set G) ≤ M)
    {a b : G} (haA : a ∈ closure (Z ∩ (M : Set G))) (hav : Commute a v) (ha1 : a ≠ 1)
    (hbA : b ∈ closure (Z ∩ (M : Set G))) (hbv : Commute b v) (hb1 : b ≠ 1) :
    IsConj (a * v) (b * v) := by
  obtain ⟨m, hmM, hm⟩ := pair_conjugator ha htM hvM hC
  let f := MulAut.conj m
  have hvi := IsInvolution.map_of_injective hv f.toMonoidHom f.injective
  obtain ⟨g, _, hg⟩ := hlocal.punctured_coset_conjugacy (f v) hm hvi
    (f a) (conj_mem_A h hmM haA) (hav.map f.toMonoidHom) (by simpa using ha1)
    (f b) (conj_mem_A h hmM hbA) (hbv.map f.toMonoidHom) (by simpa using hb1)
  have hi : IsConj (f (a * v)) (f (b * v)) := by
    rw [map_mul, map_mul]
    exact isConj_iff.mpr ⟨g, hg⟩
  have hh := f.symm.toMonoidHom.map_isConj hi
  change IsConj (f.symm (f (a * v))) (f.symm (f (b * v))) at hh
  simpa only [MulEquiv.symm_apply_apply] using hh

omit [Finite G] in
private theorem centralizes_of_no_shear (h : IsProductDisconnected Z M)
    [IsElementaryAbelian 2 (closure (Z ∩ (M : Set G)))]
    {u : G} (hu : PFAppendixIII.IsInvolution u) (huM : u ∈ M)
    (hn : ∀ a ∈ closure (Z ∩ (M : Set G)), Commute a u → a ≠ 1 → ¬ IsConj u (a * u)) :
    u ∈ centralizer (closure (Z ∩ (M : Set G)) : Set G) := by
  intro x hx
  let y := MulAut.conj u x
  have hy : y ∈ closure (Z ∩ (M : Set G)) := conj_mem_A h huM hx
  have hx2 : x ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian x hx
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hx2)
  have hxy : x * y = y * x := setLike_mul_comm hx hy
  have huy : MulAut.conj u y = x := by
    simp only [y, MulAut.conj_apply, hu.inv_eq_self]
    calc
      u * (u * x * u) * u = (u * u) * x * (u * u) := by group
      _ = x := by simp [← pow_two, hu.sq_eq_one]
  have hfixed : MulAut.conj u (x * y) = x * y := by
    rw [map_mul, huy]
    exact hxy.symm
  have hcomm : Commute (x * y) u := (mul_inv_eq_iff_eq_mul.mp hfixed).symm
  have hconj : IsConj u ((x * y) * u) := by
    apply isConj_iff.mpr
    refine ⟨x, ?_⟩
    change x * u * x⁻¹ = (x * (u * x * u⁻¹)) * u
    rw [hxi]
    group
  have he : x * y = 1 := by
    by_contra he
    exact hn (x * y) ((Subgroup.closure _).mul_mem hx hy) hcomm he hconj
  have hye : y = x := by
    have hh := eq_inv_iff_mul_eq_one.mpr he
    exact inv_injective (hh.symm.trans hxi.symm)
  have hf : MulAut.conj u x = x := hye
  exact (mul_inv_eq_iff_eq_mul.mp hf).symm

private theorem conjugate_centralizes_A
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {u v : G} (hu : PFAppendixIII.IsInvolution u) (huM : u ∈ M)
    (huA : u ∈ centralizer (closure (Z ∩ (M : Set G)) : Set G))
    (hv : IsConj u v) (hvM : v ∈ M) :
    v ∈ centralizer (closure (Z ∩ (M : Set G)) : Set G) := by
  have hvI : PFAppendixIII.IsInvolution v := by
    obtain ⟨g, rfl⟩ := isConj_iff.mp hv
    exact IsInvolution.map_of_injective hu (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  obtain ⟨S, hSM, hf⟩ := r.fusion
  obtain ⟨m, hm⟩ := involution_fusion_in_subgroup S hSM hf hu hvI huM hvM hv
  intro a ha
  have haA : (m : G)⁻¹ * a * m ∈ closure (Z ∩ (M : Set G)) := by
    simpa only [MulAut.conj_apply, inv_inv] using conj_mem_A h (M.inv_mem m.property) ha
  have hh := congrArg (MulAut.conj (m : G)) (mem_centralizer_iff.mp huA _ haA)
  have hmu : MulAut.conj (m : G) u = v := hm
  have hma : MulAut.conj (m : G) ((m : G)⁻¹ * a * m) = a := by
    simp [MulAut.conj_apply, mul_assoc]
  simpa only [map_mul, hmu, hma] using hh

private theorem confinement
    (h : IsProductDisconnected Z M) (ha : ResidualAction Z M) {z t u : G}
    (hlocal : ResidualCentralizerLocalData Z M z t) (htM : t ∉ M)
    [IsElementaryAbelian 2 (closure (Z ∩ (M : Set G)))]
    (hlarge : 2 < Nat.card (closure (Z ∩ (M : Set G))))
    (hu : PFAppendixIII.IsInvolution u) (huM : u ∈ M) (huZ : u ∉ Z)
    (hZ : Z ∩ (M : Set G) = (closure (Z ∩ (M : Set G)) : Set G) \ {1})
    (huA : u ∈ centralizer (closure (Z ∩ (M : Set G)) : Set G))
    (hn : ∀ a ∈ closure (Z ∩ (M : Set G)), Commute a u → a ≠ 1 → ¬ IsConj u (a * u))
    {a : G} (haA : a ∈ closure (Z ∩ (M : Set G))) (ha1 : a ≠ 1) :
    centralizer ({a * u} : Set G) ≤ M := by
  classical
  let A := closure (Z ∩ (M : Set G))
  have hc (x : G) (hx : x ∈ A) : Commute x u := mem_centralizer_iff.mp huA x hx
  have haZ : a ∈ Z := (show a ∈ Z ∩ (M : Set G) by rw [hZ]; exact ⟨haA, ha1⟩).1
  have hau : PFAppendixIII.IsInvolution (a * u) := by
    refine ⟨?_, ?_⟩
    · intro he
      have heau : a = u := by simpa only [hu.inv_eq_self] using eq_inv_iff_mul_eq_one.mpr he
      exact huZ (heau ▸ haZ)
    · rw [(hc a haA).mul_pow, elemPow_eq_one_of_isElementaryAbelian a haA,
        hu.sq_eq_one, one_mul]
  by_contra hC
  let : Fintype A := Fintype.ofFinite A
  obtain ⟨b, hb1, hba⟩ := ENat.exists_ne_ne_of_three_le
    (α := A) (by rw [ENat.card_eq_coe_fintype_card, Fintype.card_eq_nat_card];
                 exact_mod_cast (show 3 ≤ Nat.card A from hlarge)) (1 : A) ⟨a, haA⟩
  have hb1' : (b : G) ≠ 1 := fun he => hb1 (Subtype.ext he)
  have hba' : (b : G) ≠ a := fun he => hba (Subtype.ext he)
  have hbaA : (b : G) * a ∈ A := A.mul_mem b.property haA
  have hba1 : (b : G) * a ≠ 1 := by
    intro he
    have hai : a⁻¹ = a := (h.involutions a haZ).inv_eq_self
    exact hba' (by simpa only [hai] using eq_inv_iff_mul_eq_one.mpr he)
  have hcomm (x : G) (hx : x ∈ A) : Commute x (a * u) :=
    (show Commute x a from setLike_mul_comm hx haA).mul_right (hc x hx)
  have he := punctured_conjugacy h ha hlocal htM hau
    (M.mul_mem (distinguishedClosure_le haA) huM) hC
    haA (hcomm a haA) ha1 hbaA (hcomm _ hbaA) hba1
  have hleft : a * (a * u) = u := by
    rw [← mul_assoc, ← pow_two, (h.involutions a haZ).sq_eq_one, one_mul]
  have hright : ((b : G) * a) * (a * u) = (b : G) * u := by
    rw [mul_assoc, hleft]
  rw [hleft, hright] at he
  exact hn b b.property (hc b b.property) hb1' he

private theorem commuting_product_class
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t u : G} (hz : z ∈ Z) (htM : t ∉ M)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (hzu : Commute z u) :
    ∀ v s : G, IsConj u v → s ∈ Z → Commute v s → IsConj (u * z) (v * s) := by
  let F := centralizerClosure Z u
  have hzF : z ∈ F := mem_centralizerClosure hz hzu
  have hfix (x : F) : MulAut.conj (x : G) u = u :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (centralizerClosure_le Z u x.property))
  have hlocal {s : G} (hs : s ∈ Z) (hc : Commute u s) : IsConj (u * z) (u * s) := by
    have hsF : s ∈ F := mem_centralizerClosure hs hc.symm
    obtain ⟨g, hg⟩ := (pair_involution_centralizerClosure_local h r htM huD hu).2.2.involutions_conjugate
      (IsInvolution.subtype (h.involutions z hz) hzF)
      (IsInvolution.subtype (h.involutions s hs) hsF)
    have hgs : MulAut.conj ((g : G)⁻¹) z = s := by
      simpa only [rightConjugateElem, MulAut.conj_apply, coe_mul, coe_inv, inv_inv]
        using congrArg Subtype.val hg
    apply isConj_iff.mpr
    refine ⟨(g : G)⁻¹, ?_⟩
    change MulAut.conj ((g : G)⁻¹) (u * z) = _
    rw [map_mul, hgs, show MulAut.conj ((g : G)⁻¹) u = u from hfix g⁻¹]
  intro v s hv hs hc
  obtain ⟨g, rfl⟩ := isConj_iff.mp hv
  have hgsZ : MulAut.conj g⁻¹ s ∈ Z := h.invariant g⁻¹ s hs
  have hcomm : Commute u (MulAut.conj g⁻¹ s) := by
    simpa [MulAut.conj_apply, mul_assoc] using hc.map (MulAut.conj g⁻¹).toMonoidHom
  have hh := (MulAut.conj g).toMonoidHom.map_isConj (hlocal hgsZ hcomm)
  have hconj : IsConj (u * z) (MulAut.conj g (u * z)) := isConj_iff.mpr ⟨g, rfl⟩
  apply hconj.trans
  simpa [MulAut.conj_apply, mul_assoc] using hh

private theorem halfOrder_support
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t u : G} (hz : z ∈ Z) (hzM : z ∈ M) (htM : t ∉ M)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (huA : u ∈ centralizer (closure (Z ∩ (M : Set G)) : Set G))
    (hP : {v : G | PFAppendixIII.IsInvolution v ∧ ∃ x ∈ Z, ∃ y ∈ Z, v = x * y} = Z) :
    ∀ a b : G, IsConj z a → IsConj u b → IsConj (u * z) (halfOrder a b) := by
  have huZ := not_mem_Z_of_mem_residualPairStabilizer h htM huD
  have hs := commuting_product_class h r hz htM huD hu
    (show Commute z u from mem_centralizer_iff.mp huA z (subset_closure ⟨hz, hzM⟩))
  have hzI := h.involutions z hz
  have hz2 : orderOf z = 2 := orderOf_eq_prime hzI.sq_eq_one hzI.ne_one
  have hu2 : orderOf u = 2 := orderOf_eq_prime hu.sq_eq_one hu.ne_one
  have hfixed {v : G} (hv : IsConj u v) : IsConj (u * z) (halfOrder z v) := by
    have hvZ : v ∉ Z := fun hvZ => huZ (mem_Z_of_isConj h hvZ hv.symm)
    have hvI : PFAppendixIII.IsInvolution v := by
      obtain ⟨g, rfl⟩ := isConj_iff.mp hv
      exact BenderSuzuki.IsInvolution.map_of_injective hu (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    have hv2 : orderOf v = 2 := orderOf_eq_prime hvI.sq_eq_one hvI.ne_one
    have hnv : ¬ IsConj z v := fun hh => hvZ (mem_Z_of_isConj h hz hh)
    have hw := halfOrder_properties hz2 hv2 hnv (IsConj.refl z) (IsConj.refl v)
    have heven : Even (orderOf (z * v)) := by
      apply Nat.not_odd_iff_even.mp
      exact fun ho => hnv (isConj_of_involutions_odd_product z v hzI.sq_eq_one hvI.sq_eq_one ho)
    have hmod : orderOf (z * v) % 4 = 2 := by
      by_contra hn
      have hdiv : orderOf (z * v) % 4 = 0 := by obtain ⟨k, hk⟩ := heven; omega
      have hzwZ := mem_Z_of_isConj h hz
        (DihedralHalfOrderClasses.preserve hz2 hv2 hdiv).1
      have hwZ : halfOrder z v ∈ Z := by
        rw [← hP]
        refine ⟨(orderOf_eq_prime_iff.mp hw.1).symm, z, hz, z * halfOrder z v, hzwZ, ?_⟩
        rw [← mul_assoc, ← pow_two, hzI.sq_eq_one, one_mul]
      have hwM : halfOrder z v ∈ M := mem_of_commute h hz hzM hw.2.1.symm
      have hvM := mem_of_commute h hwZ hwM hw.2.2
      have hvc := conjugate_centralizes_A h r hu huD.1 huA hv hvM
      have hcz : Commute z v := mem_centralizer_iff.mp hvc z (subset_closure ⟨hz, hzM⟩)
      have hp : (z * v) ^ 2 = 1 := by rw [hcz.mul_pow, hzI.sq_eq_one, hvI.sq_eq_one, one_mul]
      have hd := orderOf_dvd_of_pow_eq_one hp
      have hl := Nat.le_of_dvd (by decide : 0 < 2) hd
      have hpos := orderOf_pos (z * v)
      omega
    have hvwZ := mem_Z_of_isConj h hz
      (DihedralHalfOrderClasses.exchange hz2 hv2 hmod).2
    have hc : Commute v (v * halfOrder z v) := (Commute.refl v).mul_right hw.2.2.symm
    have hh := hs v (v * halfOrder z v) hv hvwZ hc
    simpa only [← mul_assoc, ← pow_two, hvI.sq_eq_one, one_mul] using hh
  intro a b ha hb
  obtain ⟨g, hg⟩ := isConj_iff.mp ha.symm
  have hgb : IsConj u (MulAut.conj g b) := hb.trans (isConj_iff.mpr ⟨g, rfl⟩)
  have hh := hfixed hgb
  have he : halfOrder z (MulAut.conj g b) = MulAut.conj g (halfOrder a b) := by
    rw [← hg]
    exact halfOrder_map (MulAut.conj g) a b
  rw [he] at hh
  exact hh.trans (isConj_iff.mpr ⟨g, rfl⟩).symm

private theorem fiber_singleton
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t u : G} (hz : z ∈ Z) (hzM : z ∈ M) (htM : t ∉ M)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (huA : u ∈ centralizer (closure (Z ∩ (M : Set G)) : Set G))
    (hn : ∀ a ∈ closure (Z ∩ (M : Set G)), Commute a u → a ≠ 1 → ¬ IsConj u (a * u))
    (hC : centralizer ({u * z} : Set G) ≤ M) :
    ∀ p : Fiber z u (u * z), p.val = (z, u) := by
  have huZ := not_mem_Z_of_mem_residualPairStabilizer h htM huD
  have hzu : ¬ IsConj z u := fun hc => huZ (mem_Z_of_isConj h hz hc)
  have hcu {a : G} (ha : a ∈ closure (Z ∩ (M : Set G))) : Commute u a :=
    (mem_centralizer_iff.mp huA a ha).symm
  have hzI := h.involutions z hz
  have hz2 : orderOf z = 2 := orderOf_eq_prime hzI.sq_eq_one hzI.ne_one
  have hu2 : orderOf u = 2 := orderOf_eq_prime hu.sq_eq_one hu.ne_one
  intro p
  let a := p.val.1
  let b := p.val.2
  have haZ : a ∈ Z := mem_Z_of_isConj h hz p.property.1
  have haI := h.involutions a haZ
  have hbI : PFAppendixIII.IsInvolution b := by
    obtain ⟨g, hg⟩ := isConj_iff.mp p.property.2.1
    have hi := BenderSuzuki.IsInvolution.map_of_injective hu
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    change PFAppendixIII.IsInvolution (g * u * g⁻¹) at hi
    change PFAppendixIII.IsInvolution p.val.2
    rwa [← hg]
  have hm := fiber_mem_centralizer hz2 hu2 hzu p
  have haM : a ∈ M := hC hm.1
  have hbM : b ∈ M := hC hm.2
  have haA : a ∈ closure (Z ∩ (M : Set G)) := subset_closure ⟨haZ, haM⟩
  have hbA := conjugate_centralizes_A h r hu huD.1 huA p.property.2.1 hbM
  have hab : Commute a b := mem_centralizer_iff.mp hbA a haA
  have habI : PFAppendixIII.IsInvolution (a * b) := by
    constructor
    · intro he
      have heab : a = b := by
        simpa only [hbI.inv_eq_self] using eq_inv_iff_mul_eq_one.mpr he
      have heba : p.val.2 = p.val.1 := heab.symm
      exact hzu (p.property.1.trans (heba ▸ p.property.2.1.symm))
    · rw [hab.mul_pow, haI.sq_eq_one, hbI.sq_eq_one, one_mul]
  have hp : a * b = u * z := by
    have ho : orderOf (a * b) = 2 := orderOf_eq_prime habI.sq_eq_one habI.ne_one
    have hf : halfOrder a b = u * z := p.property.2.2
    simpa only [halfOrder_def, ho, Nat.reduceDiv, pow_one] using hf
  have hba : b = (u * z) * a := by
    rw [← hp, hab.eq, mul_assoc, ← pow_two, haI.sq_eq_one, mul_one]
  have hub : Commute u b := by
    rw [hba]
    exact ((Commute.refl u).mul_right (hcu (subset_closure ⟨hz, hzM⟩))).mul_right (hcu haA)
  have hubprod : u * b = z * a := by
    rw [hba, ← mul_assoc, ← mul_assoc, ← pow_two, hu.sq_eq_one, one_mul]
  have hbu : b = u := by
    by_contra hne
    have hprodA : u * b ∈ closure (Z ∩ (M : Set G)) := by
      rw [hubprod]
      exact (Subgroup.closure _).mul_mem (subset_closure ⟨hz, hzM⟩) haA
    have hprod1 : u * b ≠ 1 := by
      intro he
      have heb : u = b := by
        simpa only [hbI.inv_eq_self] using eq_inv_iff_mul_eq_one.mpr he
      exact hne heb.symm
    have hprodcomm : Commute (u * b) u := ((Commute.refl u).mul_right hub).symm
    have he : (u * b) * u = b := by rw [hub.eq, mul_assoc, ← pow_two, hu.sq_eq_one, mul_one]
    exact hn (u * b) hprodA hprodcomm hprod1 (he.symm ▸ p.property.2.1)
  have haz : a = z := by
    rw [hbu] at hp
    have hc : Commute u z := hcu (subset_closure ⟨hz, hzM⟩)
    exact mul_right_cancel (hp.trans hc.eq)
  exact Prod.ext haz hbu

end ResidualShearing

/-- GLS4, Chapter 2, Lemma 12.7: every involution of the two-point
stabilizer shears. The local centralizers need not collapse to `L`.
Failure of shearing gives the single supported Thompson fiber of size one,
forcing the two mixed classes to commute and contradicting generation. -/
public theorem proper_residualGenerated_shearing_of_local
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hlocal : ResidualCentralizerLocalData Z M z t) :
    ResidualCentralizerShearing Z M t := by
  obtain ⟨n, hn, _, _, _, _, _, _, hA, hcard, hZ, hP, _⟩ :=
    proper_residualGenerated_structure h r ha hz hzM ht htM hL heven
  let : IsElementaryAbelian 2 (closure (Z ∩ (M : Set G))) := hA
  intro u huD hu a haA hau
  by_cases ha1 : a = 1
  · subst a
    simpa only [one_mul] using IsConj.refl u
  by_contra hnot
  have hns : ∀ b ∈ closure (Z ∩ (M : Set G)), Commute b u → b ≠ 1 → ¬ IsConj u (b * u) := by
    intro b hb hbu hb1 hconj
    obtain ⟨g, _, hg⟩ := hlocal.punctured_coset_conjugacy u huD hu b hb hbu hb1 a haA hau ha1
    exact hnot (hconj.trans (isConj_iff.mpr ⟨g, hg⟩))
  have huA := ResidualShearing.centralizes_of_no_shear h.disconnected hu huD.1 hns
  have hzu : Commute z u := mem_centralizer_iff.mp huA z (subset_closure ⟨hz, hzM⟩)
  have hlarge : 2 < Nat.card (closure (Z ∩ (M : Set G))) := by
    rw [hcard]
    have hfour := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
    norm_num at hfour
    omega
  have hC : centralizer ({u * z} : Set G) ≤ M := by
    rw [← hzu.eq]
    exact ResidualShearing.confinement h.disconnected ha hlocal htM hlarge hu huD.1
      (not_mem_Z_of_mem_residualPairStabilizer h.disconnected htM huD) hZ huA hns
      (subset_closure ⟨hz, hzM⟩) (h.disconnected.involutions z hz).ne_one
  have hs := ResidualShearing.halfOrder_support h.disconnected r hz hzM htM huD hu huA hP
  have hf := ResidualShearing.fiber_singleton h.disconnected r hz hzM htM huD hu huA hns hC
  have hgen : closure Z ≤ centralizer ({u} : Set G) := by
    rw [closure_le]
    intro b hb
    exact mem_centralizer_singleton_iff.mpr
      (commute_of_singleton_halfOrder_fiber z u (u * z) hzu hs hf
        (r.one_class z hz b hb) (IsConj.refl u)).eq
  have htop : centralizer ({u} : Set G) = ⊤ := top_le_iff.mp (r.generated ▸ hgen)
  have huC : u ∈ center G := centralizer_eq_top_iff_subset.mp htop (Set.mem_singleton u)
  rcases r.simple.eq_bot_or_eq_top_of_normal (center G) inferInstance with hc | hc
  · exact hu.ne_one (mem_bot.mp (hc ▸ huC))
  · have hzC : z ∈ center G := hc ▸ mem_top z
    exact htM (h.disconnected.centralizer_le hz hzM
      (mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hzC t)))

/-- The last assertion of Lemma 12.7: the product of a conjugate of an
involution of `D` and a commuting distinguished involution is in the former
class. This is the mixed-pair fusion used in the following Thompson counts. -/
public theorem proper_residualGenerated_commuting_mixed_fusion_of_local
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hlocal : ResidualCentralizerLocalData Z M z t)
    {u v s : G} (huD : u ∈ residualPairStabilizer M t)
    (hu : PFAppendixIII.IsInvolution u) (hv : IsConj u v) (hs : s ∈ Z)
    (hvs : Commute v s) : IsConj u (v * s) := by
  obtain ⟨n, _, _, _, _, _, _, _, _, _, hZ, _⟩ :=
    proper_residualGenerated_structure h r ha hz hzM ht htM hL heven
  obtain ⟨k, hk, hcard, _⟩ := (hlocal.quotient_models u huD hu).2
  let C := closure (Z ∩ (M : Set G)) ⊓ centralizer ({u} : Set G)
  have hlarge : 1 < Nat.card C := by
    change 1 < Nat.card (closure (Z ∩ (M : Set G)) ⊓ centralizer ({u} : Set G) : Subgroup G)
    rw [hcard]
    have hfour := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk
    norm_num at hfour
    omega
  let : Nontrivial C := Finite.one_lt_card_iff_nontrivial.mp hlarge
  obtain ⟨a, ha1⟩ := exists_ne (1 : C)
  have ha1' : (a : G) ≠ 1 := fun he => ha1 (Subtype.ext he)
  have haZ : (a : G) ∈ Z := (show (a : G) ∈ Z ∩ (M : Set G) by
    rw [hZ]; exact ⟨a.property.1, ha1'⟩).1
  have hau : Commute (a : G) u := mem_centralizer_singleton_iff.mp a.property.2
  have hshear := proper_residualGenerated_shearing_of_local h r ha hz hzM ht htM hL heven hlocal
    u huD hu a a.property.1 hau
  rw [hau.eq] at hshear
  exact hshear.trans (ResidualShearing.commuting_product_class h.disconnected r haZ htM huD hu hau
    v s hv hs hvs)

end BenderSuzuki.ZD
