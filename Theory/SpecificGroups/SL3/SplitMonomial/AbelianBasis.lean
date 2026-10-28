module

public import Theory.SpecificGroups.SL3.SplitMonomial.InvariantBasis
public import Theory.SpecificGroups.SL3.SplitMonomial.AbelianBasis.Clifford
public import Theory.SpecificGroups.SL3.SplitMonomial.AbelianBasis.Irreducible
public import Theory.SpecificGroups.SL3.SplitMonomial.AbelianBasis.SingerExclusion

/-!
# An invariant line basis from a noncentral abelian normal subgroup

The nonabelian three-subgroup makes the overgroup absolutely irreducible.
Its full ambient Sylow two-subgroup excludes an irreducible abelian normal
restriction by the involution determinant argument. Clifford theory then
supplies three simple lines over the original coefficient field. Equal
multiplicities make them either all isomorphic or pairwise nonisomorphic.
The first possibility would make the normal subgroup scalar, contrary to
noncentrality. The second makes the lines unique and hence permuted by the
overgroup. Choosing their basis vectors gives the required actual basis.

Normality is relative to the overgroup throughout. The existence of the
noncentral abelian normal subgroup is an explicit input; this module proves
the invariant-basis step of the source placement argument.

Source: GLS3, proof of Theorem 6.5.3, decomposition (6.5.1) and cases (b–c),
`refs/KGroup/GLS3/chapter6.tex`; Aschbacher–Smith, proof of Proposition 1.3.4,
printed p.511 (PDF p.528 of `refs/quasithin.pdf`).
-/

open Representation
namespace Matrix.SL3.SplitMonomial
variable {F : Type*} [Field F] [Finite F]

/-- A noncentral relatively normal subgroup with reducible restriction supplies
an invariant line basis for an irreducible subgroup of SL₃. -/
public theorem hasInvariantBasis_of_reducible_normal
    (H A : Subgroup (SpecialLinearGroup (Fin 3) F))
    (hAH : A ≤ H) (hnormal : (A.subgroupOf H).Normal)
    (hnoncentral : ¬ A ≤ Subgroup.center (SpecialLinearGroup (Fin 3) F))
    (hirr : IsIrreducible ((specialLinearNatural (k := F) 3).comp H.subtype))
    (hred : ¬ IsIrreducible ((specialLinearNatural (k := F) 3).comp A.subtype)) :
    HasInvariantBasis H := by
  let ρ := (specialLinearNatural (k := F) 3).comp H.subtype
  let N := A.subgroupOf H
  let : N.Normal := hnormal
  have hred' : ¬ IsIrreducible (ρ.comp N.subtype) := by
    intro hi
    exact hred ((RepEquiv.irreducible_iff_group_iso
      (Subgroup.subgroupOfEquivOfLe hAH) (fun _ _ => rfl)).mp hi)
  have hscalar : ¬ ∀ n : N, ∃ c : F, ρ n.val = c • LinearMap.id := by
    intro hs
    apply hnoncentral
    intro a ha
    obtain ⟨c, hc⟩ := hs ⟨⟨a, hAH ha⟩, ha⟩
    have hc' : specialLinearNatural 3 a = c • LinearMap.id := hc
    rw [Subgroup.mem_center_iff]
    intro z
    apply specialLinearNatural_injective 3
    simp only [map_mul, hc']
    ext v
    simp [Module.End.mul_apply]
  obtain ⟨b, hb⟩ := AbelianBasis.exists_permuted_basis_of_reducible_normal
    ρ N hirr (by simp) hred' hscalar
  refine ⟨b, fun g hg i => ?_⟩
  obtain ⟨j, hj⟩ := hb ⟨g, hg⟩ i
  have hm : g • b i ∈ Submodule.span F {b j} := by
    rw [← hj]
    exact ⟨b i, Submodule.subset_span (Set.mem_singleton (b i)), rfl⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
  refine ⟨j, c, ?_, hc.symm⟩
  intro hc0
  have hzero : g • b i = 0 := by rw [← hc, hc0, zero_smul]
  apply b.ne_zero i
  have hz := congrArg (fun v => g⁻¹ • v) hzero
  simpa only [inv_smul_smul, smul_zero] using hz

/-- A noncentral abelian subgroup normal in the source overgroup supplies an
actual invariant basis over the prime field. The full ambient Sylow two-subgroup
excludes the irreducible abelian alternative. -/
public theorem hasInvariantBasis_of_noncentralAbelianNormal
    {p : ℕ} (hp : p.Prime) (_hpodd : Odd p) (hp3 : 3 < p) (_hpmod : p % 3 = 1)
    (hF : Nat.card F = p) (T : Sylow 2 (SpecialLinearGroup (Fin 3) F))
    (H : Subgroup (SpecialLinearGroup (Fin 3) F)) (_hsolv : Group.IsSolvable H)
    (hTH : (T : Subgroup _) ≤ H)
    (hU : ∃ U : Subgroup (SpecialLinearGroup (Fin 3) F),
      U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U)
    (hA : HasNoncentralAbelianNormal H) : HasInvariantBasis H := by
  let : Fact p.Prime := ⟨hp⟩
  let := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have h2 : (2 : F) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime F (p := p) Nat.prime_two
      (ne_of_gt (lt_trans (by decide : 2 < 3) hp3))
  let : IsAbsolutelyIrreducible ((specialLinearNatural (k := F) 3).comp H.subtype) :=
    natural_isAbsolutelyIrreducible_of_nonabelian_three_subgroup (ne_of_gt hp3) H hU
  have hirr : IsIrreducible ((specialLinearNatural (k := F) 3).comp H.subtype) :=
    IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible _
  obtain ⟨A, hAH, hnormal, hab, hnoncentral⟩ := hA
  let : IsMulCommutative A := hab
  apply hasInvariantBasis_of_reducible_normal H A hAH hnormal hnoncentral hirr
  exact AbelianBasis.not_irreducible_of_sylow_two_le_normalizer h2 T A
    (hTH.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hAH).mp hnormal))

end Matrix.SL3.SplitMonomial
