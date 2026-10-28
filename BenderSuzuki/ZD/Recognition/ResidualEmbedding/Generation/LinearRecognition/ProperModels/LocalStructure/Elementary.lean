module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.Foundations

/-!
# Elementary local structure of the proper residual subgroup

In proper `L = ⟨z,t,[O₂′(D),t]⟩`, all involutions belong to `Z` by
local strong embedding. Assuming `A = ⟨Z ∩ M⟩ ≤ L`, an involution product
of distinguished elements lies in `Z`: conjugate one factor into `M`, use
commutation to put both factors in `A`, and apply the local involution theorem.
A commuting pair supplied by minimality proves the reverse inclusion `Z ≤ P`.

The same local theorem identifies the ambient image of the involution core
of `M ∩ L` with `A`. Exponent two then identifies `Z ∩ M` with `A` minus
its identity. The exponent assumption is a remaining model calculation,
not an assertion here that the elementary abelian clause is already proved.

Finally, internal involution conjugacy gives the genuine set-product
factorization `N_G(L) = L (M ∩ N_G(L))`. Replacing the second factor by `D`
requires the additional Borel geometry of the actual models.

Source: GLS, Volume 4, Chapter 2, Lemma 12.2(b–d),
`refs/KGroup/GLS4/Chapter2.tex`, lines 2007–2032.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

omit [Finite G] in
/-- Containment in `L` identifies the two distinguished closures, in ambient `G`. -/
public theorem distinguishedClosure_eq_local_of_le (L : Subgroup G)
    (hAL : closure (Z ∩ (M : Set G)) ≤ L) :
    closure (Z ∩ ((M ⊓ L : Subgroup G) : Set G)) = closure (Z ∩ (M : Set G)) := by
  apply le_antisymm
  · exact closure_mono fun _ hx => ⟨hx.1, hx.2.1⟩
  · apply (closure_le _).mpr
    intro x hx
    exact subset_closure ⟨hx.1, hx.2, hAL (subset_closure hx)⟩

/-- An involution product of distinguished elements is distinguished, using local strong embedding. -/
public theorem distinguished_mul_mem_of_involution
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    {x y : G} (hx : x ∈ Z) (hy : y ∈ Z) (hxy : PFAppendixIII.IsInvolution (x * y)) :
    x * y ∈ Z := by
  have hc : Commute x y := by
    have he := hxy.inv_eq_self
    rw [mul_inv_rev, (h.involutions x hx).inv_eq_self,
      (h.involutions y hy).inv_eq_self] at he
    exact he.symm
  obtain ⟨g, hg⟩ := isConj_iff.mp (r.one_class x hx z hz)
  have hgx : MulAut.conj g x = z := hg
  have hy' : MulAut.conj g y ∈ Z := h.invariant g y hy
  have hc' : Commute z (MulAut.conj g y) := by
    rw [← hgx]
    exact hc.map (MulAut.conj g).toMonoidHom
  have hyM : MulAut.conj g y ∈ M := mem_of_commute h hz hzM hc'
  have hprodL : MulAut.conj g (x * y) ∈ residualGenerated M z t := by
    rw [map_mul, hgx]
    exact (residualGenerated M z t).mul_mem
      (hAL (subset_closure ⟨hz, hzM⟩)) (hAL (subset_closure ⟨hy', hyM⟩))
  have hprodI : PFAppendixIII.IsInvolution (MulAut.conj g (x * y)) :=
    BenderSuzuki.IsInvolution.map_of_injective hxy (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  have hprodZ := (isInvolution_iff_mem_Z_in_proper_residualGenerated h r hz hzM ht htM hL hprodL).mp hprodI
  simpa [MulAut.conj_apply, mul_assoc] using h.invariant g⁻¹ _ hprodZ

/-- The full equality `P = Z` of Lemma 12.2(c), conditional only on the permitted containment `A ≤ L`. -/
public theorem involutionProducts_eq_distinguished
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t) :
    {u : G | PFAppendixIII.IsInvolution u ∧ ∃ x ∈ Z, ∃ y ∈ Z, u = x * y} = Z := by
  apply Set.Subset.antisymm
  · rintro _ ⟨hi, x, hx, y, hy, rfl⟩
    exact distinguished_mul_mem_of_involution h.disconnected r hz hzM ht htM hL hAL hx hy hi
  · intro u hu
    obtain ⟨y, hy, hyM, hne, hc⟩ := exists_commuting_distinguished_of_minimal h r hz hzM
    have hyzI : PFAppendixIII.IsInvolution (y * z) := by
      constructor
      · intro he
        have he' : y = z := by
          simpa only [(h.disconnected.involutions z hz).inv_eq_self] using
            (eq_inv_iff_mul_eq_one.mpr he)
        exact hne he'.symm
      · rw [hc.symm.mul_pow, (h.disconnected.involutions y hy).sq_eq_one,
          (h.disconnected.involutions z hz).sq_eq_one, one_mul]
    have hyzZ := distinguished_mul_mem_of_involution h.disconnected r hz hzM ht htM hL hAL hy hz hyzI
    obtain ⟨g, hg⟩ := isConj_iff.mp (r.one_class z hz u hu)
    refine ⟨h.disconnected.involutions u hu, MulAut.conj g y,
      h.disconnected.invariant g y hy, MulAut.conj g (y * z),
      h.disconnected.invariant g (y * z) hyzZ, ?_⟩
    rw [← map_mul]
    have hyy : y * y = 1 := by simpa only [pow_two] using (h.disconnected.involutions y hy).sq_eq_one
    simpa only [← mul_assoc, hyy, one_mul, MulAut.conj_apply] using hg.symm

/-- The involution core of the local intersection maps to the distinguished closure in `G`. -/
public theorem distinguishedClosure_eq_involutionCore_local
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t) :
    (involutionCore (M ⊓ residualGenerated M z t : Subgroup G)).map
      (M ⊓ residualGenerated M z t).subtype = closure (Z ∩ (M : Set G)) := by
  rw [involutionCore_eq_closure, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, y.property.1⟩
    apply (isInvolution_iff_mem_Z_in_proper_residualGenerated h r hz hzM ht htM hL y.property.2).mp
    exact BenderSuzuki.IsInvolution.map_of_injective hy
      (M ⊓ residualGenerated M z t).subtype Subtype.val_injective
  · intro hx
    exact ⟨⟨x, hx.2, hAL (subset_closure hx)⟩,
      BenderSuzuki.IsInvolution.subtype (h.involutions x hx.1)
        (show x ∈ M ⊓ residualGenerated M z t from ⟨hx.2, hAL (subset_closure hx)⟩), rfl⟩

/-- Once the model calculation proves exponent two, the nonidentity elements of `A` are exactly `Z ∩ M`. -/
public theorem distinguished_eq_nonidentity_of_exponent_two
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hA2 : ∀ a ∈ closure (Z ∩ (M : Set G)), a ^ 2 = 1) :
    Z ∩ (M : Set G) = (closure (Z ∩ (M : Set G)) : Set G) \ {1} := by
  ext x
  constructor
  · intro hx
    exact ⟨subset_closure hx, (h.involutions x hx.1).ne_one⟩
  · rintro ⟨hx, hne⟩
    exact ⟨(isInvolution_iff_mem_Z_in_proper_residualGenerated h r hz hzM ht htM hL
      (hAL hx)).mp ⟨hne, hA2 x hx⟩, distinguishedClosure_le hx⟩

open scoped Pointwise in
/-- Local involution conjugacy factors the ambient normalizer as an actual product of subgroups. -/
public theorem normalizer_eq_mul_inter_of_local_strongEmbedding
    (h : IsProductDisconnected Z M) (L : Subgroup G)
    (hs : IsStronglyEmbedded (M.comap L.subtype))
    {z : G} (hz : z ∈ Z) (hzM : z ∈ M) (hzL : z ∈ L) :
    (normalizer (L : Set G) : Set G) =
      (L : Set G) * ((M ⊓ normalizer (L : Set G) : Subgroup G) : Set G) := by
  ext g
  constructor
  · intro hg
    have hxL : MulAut.conj g z ∈ L := (mem_normalizer_iff.mp hg z).mp hzL
    have hxI : PFAppendixIII.IsInvolution (MulAut.conj g z) :=
      h.involutions _ (h.invariant g z hz)
    obtain ⟨l, hl⟩ := hs.involutions_conjugate
      (BenderSuzuki.IsInvolution.subtype hxI hxL)
      (BenderSuzuki.IsInvolution.subtype (h.involutions z hz) hzL)
    have he : MulAut.conj ((l : G)⁻¹ * g) z = z := by
      have he := congrArg Subtype.val hl
      simpa only [rightConjugateElem, coe_mul, coe_inv, MulAut.conj_apply,
        mul_inv_rev, inv_inv, mul_assoc] using he
    have hmM : (l : G)⁻¹ * g ∈ M :=
      (h.conjugate_mem_iff z hz hzM _).mp (he.symm ▸ hzM)
    apply Set.mem_mul.mpr
    exact ⟨l, l.property, (l : G)⁻¹ * g,
      ⟨hmM, (normalizer (L : Set G)).mul_mem
        ((normalizer (L : Set G)).inv_mem (L.le_normalizer l.property)) hg⟩,
      by group⟩
  · rintro ⟨l, hl, m, hm, rfl⟩
    exact (normalizer (L : Set G)).mul_mem (L.le_normalizer hl) hm.2
end BenderSuzuki.ZD
