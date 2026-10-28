module
public import Theory.GroupAction.QuotientCommutatorPairing
public import Theory.GroupAction.TwoGroupEquivariantFamily

/-!
# Small irreducible quotient commutator families vanish

Let P normalize B,U,V,Z in a finite group, with B centralizing V,
Z≤V≤B, [B,U]≤V and [V,U]≤Z. No commutativity or exponent condition
on B is needed; the original elementary-B theorem is retained as a wrapper. Suppose E is normal in P,
P/E is a two-group, and [B,E]≤V. On the literal quotient V/Z, retain the
supplied conjugation action and its invariant-subgroup irreducibility.
If every individual cyclic commutator image [<b>,U] in V/Z has cardinality
strictly smaller than V/Z, then [B,U]≤Z.

The quotient commutator pairing descends through its actual kernel
to an injective family in Hom(U,V/Z). This makes the family quotient
elementary abelian of exponent two, even when B is noncommutative. Simultaneous conjugation preserves that kernel and
gives the descended action. V lies in the pairing kernel, so E acts trivially
on this family and its actual automorphism image is a quotient of P/E.
The two-group fixed-point argument for small equivariant families forces
the descended family to be trivial. The source applications are the actual
Y∨V terminal family in Stellmacher (10.1)(16), printed p.64, and the
C∨V first-module family in (20), printed p.65.
No containment B≤P or U≤P and no faithfulness of the supplied action is used.
-/

namespace Subgroup
open scoped Pointwise commutatorElement IsMulCommutative

public theorem commutator_le_of_small_irreducible_centralizing_family
    {G : Type*} [Group G] [Finite G]
    (P B U V Z E : Subgroup G)
    (_hZV : Z ≤ V) (hVB : V ≤ B) (hBV : B ≤ centralizer (V:Set G))
    (hPB : P ≤ normalizer (B:Set G)) (hPU : P ≤ normalizer (U:Set G))
    (hPV : P ≤ normalizer (V:Set G)) (_hPZ : P ≤ normalizer (Z:Set G))
    (_hEP : E ≤ P) [hEN : (E.subgroupOf P).Normal]
    (hptwo : IsPGroup 2 (P ⧸ E.subgroupOf P))
    (hBU : ⁅B,U⁆ ≤ V) (hVU : ⁅V,U⁆ ≤ Z) (hBE : ⁅B,E⁆ ≤ V)
    [hN : (Z.subgroupOf V).Normal]
    [hW : IsElementaryAbelian 2 (V ⧸ Z.subgroupOf V)]
    (action : P →* MulAut (V ⧸ Z.subgroupOf V))
    (haction : ∀ p:P, ∀v:V,
      action p (QuotientGroup.mk' (Z.subgroupOf V) v) =
        QuotientGroup.mk' (Z.subgroupOf V)
          ⟨(p:G)*(v:G)*(p:G)⁻¹,
            (Subgroup.mem_normalizer_iff.mp (hPV p.property) v).mp v.property⟩)
    (hirreducible : ∀ D : Subgroup (V ⧸ Z.subgroupOf V),
      (∀ p:P, ∀v, v∈D → action p v ∈ D) → D=⊥ ∨ D=⊤)
    (hsmall : ∀ b:B,
      Nat.card ((⁅Subgroup.zpowers (b:G),U⁆.subgroupOf V).map
        (QuotientGroup.mk' (Z.subgroupOf V))) < Nat.card (V ⧸ Z.subgroupOf V)) :
    ⁅B,U⁆ ≤ Z := by
  classical
  let W := V ⧸ Z.subgroupOf V
  let _ : CommGroup W := IsMulCommutative.instCommGroup
  let _ : Subgroup.Normalizes P B := ⟨hPB⟩
  let _ : Subgroup.Normalizes P U := ⟨hPU⟩
  let _ : MulDistribMulAction P B := Subgroup.conjMulDistribMulActionOfLeNormalizer P B hPB
  let _ : MulDistribMulAction P U := Subgroup.conjMulDistribMulActionOfLeNormalizer P U hPU
  let _ : MulDistribMulAction P W := MulDistribMulAction.compHom W action
  let f : B →* (U →* W) := centralQuotientCommutatorPairing B U V Z hVB hBV hBU hVU
  have hequiv (p:P) (b:B) (u:U) : f (p • b) (p • u) = p • f b u := by
    change centralQuotientCommutatorPairing B U V Z hVB hBV hBU hVU (p • b) (p • u) =
      action p (centralQuotientCommutatorPairing B U V Z hVB hBV hBU hVU b u)
    rw [centralQuotientCommutatorPairing_apply,centralQuotientCommutatorPairing_apply,haction]
    congr 1
    apply Subtype.ext
    change ⁅(p:G)*(b:G)*(p:G)⁻¹,(p:G)*(u:G)*(p:G)⁻¹⁆ =
      (p:G)*⁅(b:G),(u:G)⁆*(p:G)⁻¹
    exact (conjugate_commutatorElement (b:G) (u:G) (p:G)).symm
  have hInvForward (p:P) (b:B) (hb:b∈f.ker) : p • b ∈ f.ker := by
    apply MonoidHom.mem_ker.mpr
    have hz := MonoidHom.mem_ker.mp hb
    ext u
    have hh := hequiv p b (p⁻¹ • u)
    simpa only [smul_inv_smul,hz,MonoidHom.one_apply,smul_one] using hh
  have hInv : IsInvariant P B f.ker := by
    constructor
    intro p b
    constructor
    · exact hInvForward p b
    · intro hb
      have hh := hInvForward p⁻¹ (p • b) hb
      simpa only [inv_smul_smul] using hh
  let A := B ⧸ f.ker
  let π : B →* A := QuotientGroup.mk' f.ker
  let family : A →* (U →* W) := QuotientGroup.kerLift f
  have hfamilyInjective : Function.Injective family := QuotientGroup.kerLift_injective f
  let _ : IsElementaryAbelian 2 A := {
    toIsMulCommutative := ⟨⟨fun a b => hfamilyInjective (by
      rw [map_mul,map_mul]
      exact mul_comm _ _)⟩⟩
    exponent_dvd_p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro a
      apply hfamilyInjective
      ext u
      rw [map_pow,map_one]
      change (family a u)^2 = 1
      exact (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 W)) _ }
  let _ : MulDistribMulAction P A := quotientMulDistribMulAction f.ker hInv
  have hπ (p:P) (b:B) : p • π b = π (p • b) := by
    let _ : MulAction.QuotientAction P f.ker := quotientAction_of_isInvariant _ hInv
    exact MulAction.Quotient.smul_coe f.ker p b
  have hfamily (b:B) : family (π b) = f b := QuotientGroup.kerLift_mk f b
  have hfamilyEquiv (p:P) (a:A) (u:U) :
      family (p • a) (p • u) = p • family a u := by
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective f.ker a
    rw [hπ,hfamily,hfamily]
    exact hequiv p b u
  have hVk : V.subgroupOf B ≤ f.ker := by
    intro v hv
    apply MonoidHom.mem_ker.mpr
    ext u
    rw [show f v u = _ from centralQuotientCommutatorPairing_apply B U V Z hVB hBV hBU hVU v u]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact hVU (Subgroup.commutator_mem_commutator hv u.property)
  let ρ := MulDistribMulAction.toMulAut P A
  have hkill : E.subgroupOf P ≤ ρ.ker := by
    intro e he
    apply MonoidHom.mem_ker.mpr
    ext a
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective f.ker a
    change e • π b = π b
    rw [hπ]
    apply QuotientGroup.eq_iff_div_mem.mpr
    apply hVk
    change (e:G)*(b:G)*(e:G)⁻¹ / (b:G) ∈ V
    have hc : ⁅(e:G),(b:G)⁆ ∈ V := by
      rw [Subgroup.commutator_comm] at hBE
      exact hBE (Subgroup.commutator_mem_commutator he b.property)
    simpa only [commutatorElement_def,div_eq_mul_inv] using hc
  let bar : (P ⧸ E.subgroupOf P) →* ρ.range := QuotientGroup.lift _ ρ.rangeRestrict
    (by simpa only [MonoidHom.ker_rangeRestrict] using hkill)
  have hbar : Function.Surjective bar := by
    intro r
    obtain ⟨p,rfl⟩ := ρ.rangeRestrict_surjective r
    exact ⟨QuotientGroup.mk' (E.subgroupOf P) p,rfl⟩
  have htwo : IsPGroup 2 ρ.range := hptwo.of_surjective bar hbar
  have hsmallFamily (a:A) : Nat.card (family a).range < Nat.card W := by
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective f.ker a
    rw [hfamily]
    change Nat.card (centralQuotientCommutatorPairing B U V Z hVB hBV hBU hVU b).range < _
    rw [centralQuotientCommutatorPairing_range]
    exact hsmall b
  have htrivial : Subsingleton A :=
    equivariant_family_subsingleton_of_small_images family (QuotientGroup.kerLift_injective f)
      hfamilyEquiv htwo hirreducible hsmallFamily
  apply Subgroup.commutator_le.mpr
  intro b hb u hu
  have hbker : (⟨b,hb⟩:B) ∈ f.ker :=
    (QuotientGroup.eq_one_iff _).mp (htrivial.elim (π ⟨b,hb⟩) 1)
  have hz := congrArg (fun k:U→*W => k ⟨u,hu⟩) (MonoidHom.mem_ker.mp hbker)
  change f ⟨b,hb⟩ ⟨u,hu⟩ = 1 at hz
  rw [show f ⟨b,hb⟩ ⟨u,hu⟩ = _ from
    centralQuotientCommutatorPairing_apply B U V Z hVB hBV hBU hVU ⟨b,hb⟩ ⟨u,hu⟩] at hz
  have hm := (QuotientGroup.eq_one_iff (N := Z.subgroupOf V) _).mp hz
  exact hm

public theorem commutator_le_of_small_irreducible_family
    {G : Type*} [Group G] [Finite G]
    (P B U V Z E : Subgroup G) [IsElementaryAbelian 2 B]
    (_hZV : Z ≤ V) (hVB : V ≤ B)
    (hPB : P ≤ normalizer (B:Set G)) (hPU : P ≤ normalizer (U:Set G))
    (hPV : P ≤ normalizer (V:Set G)) (_hPZ : P ≤ normalizer (Z:Set G))
    (_hEP : E ≤ P) [hEN : (E.subgroupOf P).Normal]
    (hptwo : IsPGroup 2 (P ⧸ E.subgroupOf P))
    (hBU : ⁅B,U⁆ ≤ V) (hVU : ⁅V,U⁆ ≤ Z) (hBE : ⁅B,E⁆ ≤ V)
    [hN : (Z.subgroupOf V).Normal]
    [hW : IsElementaryAbelian 2 (V ⧸ Z.subgroupOf V)]
    (action : P →* MulAut (V ⧸ Z.subgroupOf V))
    (haction : ∀ p:P, ∀v:V,
      action p (QuotientGroup.mk' (Z.subgroupOf V) v) =
        QuotientGroup.mk' (Z.subgroupOf V)
          ⟨(p:G)*(v:G)*(p:G)⁻¹,
            (Subgroup.mem_normalizer_iff.mp (hPV p.property) v).mp v.property⟩)
    (hirreducible : ∀ D : Subgroup (V ⧸ Z.subgroupOf V),
      (∀ p:P, ∀v, v∈D → action p v ∈ D) → D=⊥ ∨ D=⊤)
    (hsmall : ∀ b:B,
      Nat.card ((⁅Subgroup.zpowers (b:G),U⁆.subgroupOf V).map
        (QuotientGroup.mk' (Z.subgroupOf V))) < Nat.card (V ⧸ Z.subgroupOf V)) :
    ⁅B,U⁆ ≤ Z := by
  have hBV : B ≤ centralizer (V:Set G) :=
    (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le hVB)
  exact commutator_le_of_small_irreducible_centralizing_family P B U V Z E
    _hZV hVB hBV hPB hPU hPV _hPZ _hEP hptwo hBU hVU hBE action haction hirreducible hsmall

end Subgroup
