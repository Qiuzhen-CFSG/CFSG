module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.PairedModule.MarkedAction
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.Definitions
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Orthogonal.FullAction

/-!
# Squares of the original marked actor

The elementary four-group image of `T_E` in the compatible natural action
makes its squares centralize `V`. Commutation of the two marked quotient
factors puts every `C_E`-conjugate of `τ` back in `T_E`. Their squares thus
centralize `V`, so `τ²` centralizes the whole original span `U = ⟨V^{C_E}⟩`.
The first coordinate of `τ` is consequently an involution; its nonidentity
follows from `τ ∉ S_E` and `Q_E ≤ S_E`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.67, printed p.1153, PDF p.1170. This argument uses the original groups
and the action image from 15.3.66(3), before the temporary replacement.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure.PairedModule.SourceAction
open Descent.QuotientIdentification GoldschmidtCore.LocalRelations
variable {G : Type*} [Group G] {V M Y T E : Subgroup G}

/-- Squares in the actual line Sylow subgroup centralize the original module. -/
theorem lineT_square_centralizes (a : OrthogonalFourBinary.NaturalAction V M)
    (hTM : T ≤ M) [IsKleinFour (actionImage a (lineT T E))]
    (t : G) (ht : t ∈ lineT T E) : t ^ 2 ∈ centralizer (V : Set G) := by
  let m : M := ⟨t, hTM ht.1⟩
  have hi : a.action m ∈ actionImage a (lineT T E) := mem_map_of_mem _ ht
  have hs : a.action m * a.action m = 1 :=
    congrArg Subtype.val (IsKleinFour.mul_self ⟨a.action m, hi⟩)
  have hk : m ^ 2 ∈ a.action.ker := by
    change a.action (m ^ 2) = 1
    rw [map_pow, pow_two]
    exact hs
  rw [action_ker a] at hk
  exact hk

/-- Marked commutation keeps every centralizer conjugate of `τ` in `T_E`. -/
theorem centralizer_conjugate_tau_mem (d : MarkedDecomposition Y T E)
    (hQS : lineQ E ≤ T ⊓ centralizer (E : Set G))
    (c : centralizer (E : Set G)) :
    (c : G)⁻¹ * d.tau * c ∈ lineT T E := by
  let cn : lineNormalizer E := inclusion (centralizer_le_normalizer (E : Set G)) c
  let tn : lineNormalizer E := ⟨d.tau, d.tau_mem.2⟩
  let f := d.equiv.toMonoidHom.comp (quotientMap E)
  have hc : f cn = (1, centralizerImageMap E c) := d.centralizer_factor c
  have ht : (f tn).2 = 1 := marked_tau_second E d
  have he : f (cn⁻¹ * tn * cn) = f tn := by
    rw [map_mul, map_mul, map_inv, hc]
    apply Prod.ext
    · simp
    · simp [ht]
  have he' : quotientMap E (cn⁻¹ * tn * cn) = quotientMap E tn := d.equiv.injective he
  have hq : (cn⁻¹ * tn * cn) / tn ∈ pCore 2 (lineNormalizer E) :=
    QuotientGroup.eq_iff_div_mem.mp he'
  have hqG : ((c : G)⁻¹ * d.tau * c) / d.tau ∈ lineQ E :=
    mem_map_of_mem (lineNormalizer E).subtype hq
  refine ⟨?_, (cn⁻¹ * tn * cn).property⟩
  have hprod := T.mul_mem (hQS hqG).1 d.tau_mem.1
  change (c : G)⁻¹ * d.tau * c ∈ T
  simpa only [div_mul_cancel] using hprod

/-- The square of `τ` centralizes the original centralizer span. -/
theorem tau_square_centralizes_span (a : OrthogonalFourBinary.NaturalAction V M)
    (d : MarkedDecomposition Y T E) (hTM : T ≤ M)
    [IsKleinFour (actionImage a (lineT T E))]
    (hspan : lineV V E = conjugateSpanBy V (lineC E))
    (hQS : lineQ E ≤ T ⊓ centralizer (E : Set G)) :
    d.tau ^ 2 ∈ centralizer (lineV V E : Set G) := by
  apply mem_centralizer_iff.mpr
  have hle : lineV V E ≤ centralizer ({d.tau ^ 2} : Set G) := by
    rw [hspan]
    apply (closure_le _).mpr
    rintro x ⟨c, hc, v, hv, rfl⟩
    have hs := lineT_square_centralizes a hTM ((c : G)⁻¹ * d.tau * c)
      (centralizer_conjugate_tau_mem d hQS ⟨c, hc⟩)
    have hh := mem_centralizer_iff.mp hs v hv
    apply mem_centralizer_singleton_iff.mpr
    have hh' := congrArg (fun z : G => c * z * c⁻¹) hh
    convert hh' using 1 <;> simp only [pow_two] <;> group
  intro u hu
  exact mem_centralizer_singleton_iff.mp (hle hu)

/-- The first marked coordinate of the original `τ` has order two. -/
theorem tau_first_order (a : OrthogonalFourBinary.NaturalAction V M)
    (d : MarkedDecomposition Y T E) (hTM : T ≤ M) (hEV : E ≤ V)
    [IsKleinFour (actionImage a (lineT T E))]
    (hQS : lineQ E ≤ T ⊓ centralizer (E : Set G))
    (htau : d.tau ∉ T ⊓ centralizer (E : Set G)) :
    orderOf (d.equiv (quotientMap E ⟨d.tau, d.tau_mem.2⟩)).1 = 2 := by
  let tn : lineNormalizer E := ⟨d.tau, d.tau_mem.2⟩
  let f := d.equiv.toMonoidHom.comp (quotientMap E)
  have hs : d.tau ^ 2 ∈ centralizer (E : Set G) :=
    centralizer_le hEV (lineT_square_centralizes a hTM d.tau d.tau_mem)
  have hs' : ((f tn).1) ^ 2 = 1 := by
    have hh := congrArg Prod.fst (d.centralizer_factor ⟨d.tau ^ 2, hs⟩)
    change (f (tn ^ 2)).1 = 1 at hh
    simpa only [map_pow, Prod.pow_fst] using hh
  have hn : (f tn).1 ≠ 1 := by
    intro he
    have hf : f tn = 1 := Prod.ext he (marked_tau_second E d)
    have hq : quotientMap E tn = 1 := d.equiv.injective (hf.trans (map_one d.equiv).symm)
    have hm : tn ∈ pCore 2 (lineNormalizer E) := (QuotientGroup.eq_one_iff tn).mp hq
    exact htau (hQS (mem_map_of_mem (lineNormalizer E).subtype hm))
  exact orderOf_eq_prime_iff.mpr ⟨hs', hn⟩
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure.PairedModule.SourceAction
