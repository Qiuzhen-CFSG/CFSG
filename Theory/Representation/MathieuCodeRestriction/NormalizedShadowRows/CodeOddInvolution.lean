module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeInvolutions
public import Theory.Representation.HexacodeAction.Field
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.CoordinateTransport
/-!
# An odd hexacode involution in every sextet Sylow subgroup

The explicit field involution lifts through the split sextet extension.
Conjugacy places it in any prescribed Sylow two-subgroup without changing
its odd sign. The full even cover and any odd element generate the entire
hexacode group, whose trivial two-core excludes odd images from a source
two-core. This provides the native actor used on the original M24-code
pair in source 8.2.8(6), printed p.719, refs/quasithin.pdf.
The underlying sextet and hexacode models are the licensed ATLAS port;
see LICENSES/ATLAS.txt.
-/
public noncomputable section
open Subgroup Atlas.Codes Representation
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open MathieuCode.SextetLayers.CoordinateTransport
namespace MathieuCode.NormalizedShadowRows.CodeInvolutions

theorem sextet_sylow_odd_involution (S : Sextet) (P : Sylow 2 (sextetStabilizer S)) :
    ∃ x : sextetStabilizer S, x ∈ P ∧ orderOf x = 2 ∧
      hexSign (nativeQuotient S x) = -1 := by
  let j : HexAutomorphisms →* sextetStabilizer S :=
    (nativeStabilizerEquiv S).toMonoidHom.comp sextetSection
  have hj (u : HexAutomorphisms) : nativeQuotient S (j u) = u := by
    change nativeQuotient S (nativeStabilizerEquiv S (sextetSection u)) = u
    rw [nativeQuotient_apply,sextetQuotient_section]
  have hi : Function.Injective j := by
    intro x y h
    have hh := congrArg (nativeQuotient S) h
    simpa only [hj] using hh
  have hu : orderOf Hexacode.fieldInvolution = 2 := by
    apply orderOf_eq_prime (by simpa only [pow_two] using Hexacode.fieldInvolution_sq)
    intro he
    have hh := Hexacode.fieldInvolution_odd
    rw [he,map_one] at hh
    contradiction
  have hx : orderOf (j Hexacode.fieldInvolution) = 2 :=
    (orderOf_injective j hi _).trans hu
  obtain ⟨y,hy⟩ := P.exists_isConj_of_orderOf_eq_prime_pow (hx.trans (pow_one 2).symm)
  obtain ⟨g,hg⟩ := isConj_iff.mp hy
  refine ⟨y,y.property,?_,?_⟩
  · rw [←hg]
    exact (MulAut.conj g).orderOf_eq _ |>.trans hx
  · rw [←hg]
    change hexSign (nativeQuotient S (g * j Hexacode.fieldInvolution * g⁻¹)) = -1
    simp only [map_mul,map_inv,hj,Hexacode.fieldInvolution_odd]
    simp [mul_comm]

/-- The full even cover together with any odd element covers all hexacode automorphisms. -/
theorem hex_surjective_of_even_and_odd {P : Type*} [Group P]
    (f : P →* HexAutomorphisms) (heven : hexSign.ker ≤ f.range)
    (t : P) (ht : hexSign (f t) = -1) : Function.Surjective f := by
  intro y
  rcases Int.units_eq_one_or (hexSign y) with hy | hy
  · exact heven hy
  · have hsign : y * (f t)⁻¹ ∈ hexSign.ker := by
      change hexSign (y * (f t)⁻¹) = 1
      simp only [map_mul,map_inv,hy,ht]
      decide
    obtain ⟨r,hr⟩ := heven hsign
    exact ⟨r*t,by rw [map_mul,hr]; simp⟩

/-- The full two-core of a hexacode cover has trivial image. An odd element
therefore escapes the product of that core with any even preimage. -/
theorem odd_not_mem_even_sup_core {P : Type*} [Group P]
    (f : P →* HexAutomorphisms) (hf : Function.Surjective f)
    (R : Subgroup P) (hR : R.map f ≤ hexSign.ker)
    (t : P) (ht : hexSign (f t) = -1) : t ∉ R ⊔ pCore 2 P := by
  have hcore : pCore 2 P ≤ f.ker := by
    have hm : (pCore 2 P).map f ≤ pCore 2 HexAutomorphisms :=
      le_sSup ⟨(inferInstance : (pCore 2 P).Normal).map f hf,pCore_isPGroup.map f⟩
    intro x hx
    have hx' := hm (mem_map_of_mem f hx)
    rwa [SextetCore.hex_core,mem_bot] at hx'
  have hle : R ⊔ pCore 2 P ≤ (hexSign.comp f).ker := sup_le
    (fun x hx => hR (mem_map_of_mem f hx))
    (fun x hx => by change hexSign (f x) = 1; rw [show f x = 1 from hcore hx,map_one])
  intro hmem
  have hone : hexSign (f t) = 1 := hle hmem
  rw [ht] at hone
  contradiction

end MathieuCode.NormalizedShadowRows.CodeInvolutions
