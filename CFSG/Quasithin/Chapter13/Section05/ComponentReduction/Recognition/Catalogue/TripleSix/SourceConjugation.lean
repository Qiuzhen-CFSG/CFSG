module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.Sections

/-!
# Detecting the outer involution in the literal source quotient

For X = KL₁T_X, an element outside the image K̂ in X/C_X(K*) induces a
non-inner automorphism of the original K*. An inner conjugator in K* lifts
through the actual star map to K, and equality of the conjugation operators
then gives equality in that same centralizer quotient. This proves the
contradiction to nonmembership, retaining every quotient map.

The result is then transported to the copy of K* inside the original K*V*.
No identification of K* and K*V*, or quotient by Z(K*) in the representation,
is used. The configuration producer supplies the stated nonmembership.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.5.21,
printed pp.923–924 (PDF pp.940–941).
-/

@[expose] public section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.TripleSix
open Section08.Source
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {K : Subgroup G}

/-- Literal nonmembership in K̂ detects outer action on K*. -/
theorem noninner_of_hat_not_mem (s : Selected D K) (h : D.Hypothesis)
    (hn : starImage D.H D.L₁ ≤ normalizer (starImage D.H K : Set (Hstar D.H)))
    (x : X D K)
    (hout : let := componentCentralizer_normal s h hn
      QuotientGroup.mk' (componentCentralizer s h) x ∉
        (K.subgroupOf (X D K)).map (QuotientGroup.mk' (componentCentralizer s h))) :
    ∀ k : starImage D.H K, componentConjugation s h hn x ≠ MulAut.conj k := by
  let := componentCentralizer_normal s h hn
  intro k hk
  obtain ⟨a, ha, hak⟩ := k.property
  let y : X D K := ⟨a.val, (show K ≤ X D K from le_sup_left) ha⟩
  have hyK : y ∈ K.subgroupOf (X D K) := ha
  have hys : starHom s h y = (k : Hstar D.H) := hak
  have hcy : componentConjugation s h hn y = MulAut.conj k := by
    apply DFunLike.ext
    intro b
    apply Subtype.ext
    change starHom s h y * (b : Hstar D.H) * (starHom s h y)⁻¹ =
      (k : Hstar D.H) * (b : Hstar D.H) * (k : Hstar D.H)⁻¹
    rw [hys]
  have hxy : x⁻¹ * y ∈ componentCentralizer s h := by
    rw [← componentConjugation_ker s h hn, MonoidHom.mem_ker,
      map_mul, map_inv, hcy, hk, inv_mul_cancel]
  have he : QuotientGroup.mk' (componentCentralizer s h) x =
      QuotientGroup.mk' (componentCentralizer s h) y := QuotientGroup.eq.mpr hxy
  apply hout
  rw [he]
  exact mem_map_of_mem _ hyK

/-- The original component, merely viewed inside the actual K*V*. -/
noncomputable def componentEquiv : component D K ≃* starImage D.H K :=
  subgroupOfEquivOfLe (show starImage D.H K ≤ actor D K from le_sup_left)

omit [Finite G] in
/-- Normalization passes to the marked component without changing actors. -/
theorem normalizes_component (v : actor D K)
    (hv : (v : Hstar D.H) ∈ normalizer (starImage D.H K : Set (Hstar D.H))) :
    v ∈ normalizer (component D K : Set (actor D K)) := by
  apply mem_normalizer_iff.mpr
  intro k
  exact (mem_normalizer_iff.mp hv) (k : Hstar D.H)

/-- An inner action on the component in K*V* would also be inner on K*.
The premise is the literal source quotient nonmembership. -/
theorem component_noninner_of_hat_not_mem (s : Selected D K) (h : D.Hypothesis)
    (hn : starImage D.H D.L₁ ≤ normalizer (starImage D.H K : Set (Hstar D.H)))
    (x : X D K) (v : actor D K) (hx : starHom s h x = (v : Hstar D.H))
    (hv : (v : Hstar D.H) ∈ normalizer (starImage D.H K : Set (Hstar D.H)))
    (hout : let := componentCentralizer_normal s h hn
      QuotientGroup.mk' (componentCentralizer s h) x ∉
        (K.subgroupOf (X D K)).map (QuotientGroup.mk' (componentCentralizer s h))) :
    ∀ k : component D K,
      (component D K).normalizerMonoidHom ⟨v, normalizes_component v hv⟩ ≠ MulAut.conj k := by
  intro k hk
  apply noninner_of_hat_not_mem s h hn x hout (componentEquiv k)
  apply DFunLike.ext
  intro b
  apply Subtype.ext
  have he := DFunLike.congr_fun hk (componentEquiv.symm b)
  have he' := congrArg (fun z : component D K => ((z : actor D K) : Hstar D.H)) he
  change (v : Hstar D.H) * (b : Hstar D.H) * (v : Hstar D.H)⁻¹ =
    ((k : actor D K) : Hstar D.H) * (b : Hstar D.H) *
      ((k : actor D K) : Hstar D.H)⁻¹ at he'
  change starHom s h x * (b : Hstar D.H) * (starHom s h x)⁻¹ = _
  rw [hx]
  exact he'

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.TripleSix
