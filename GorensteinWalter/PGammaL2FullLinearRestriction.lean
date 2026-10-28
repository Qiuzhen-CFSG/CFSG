module
public import GorensteinWalter.PGammaL2Subgroups

/-!
# Restricting the original projective map to its full linear layer

Let f map a finite group to PGammaL2(F), with N contained in L, the image
of L linear and the image of N the canonical PSL2 subgroup. If ker(f)N
has relative index two in L, then restricting f gives a surjective PGL2
map on L. Its kernel is the actual restriction of ker(f), and its inverse
image of the canonical PSL2 range is the actual restriction of ker(f)N.
The original element equation f(l)=inl(phi(l)) is retained. The general
linear-image endpoint omits the index and core-image assumptions and returns
the same restriction and kernel identity without claiming surjectivity;
this covers the proper central-product branch in the final field lift.

The image/comap index identity makes PSL2 have index two in f(L), as it
does in the full PGL2 layer. Multiplicativity of relative indices forces
f(L) to be that full layer. Corestrict f and use the canonical equivalence
of PGL2 with its image in PGammaL2; its element equation proves the kernel
and inverse-image identities. No new quotient recognition replaces f.

Source: Alperin--Brauer--Gorenstein II.3 Proposition 3, article pp25--26.
This provides the original-group projection for the full matrix extension
comparison, while preserving the projective map used later to lift the
odd coefficient action. Group and field universes are independent, and
all odd prime powers including three remain.
-/

namespace GorensteinWalter

public theorem exists_pgl2_restriction_of_linear_layer
    {H F : Type*} [Group H] [Field F]
    (f : H →* PGammaL2 F) (L : Subgroup H)
    (hlinear : L.map f ≤ pGammaL2PGLRange F) :
    ∃ φ : L →* PGL2 F,
      (∀ l : L, f l = SemidirectProduct.inl (φ l)) ∧
      φ.ker = f.ker.subgroupOf L := by
  let t : L →* pGammaL2PGLRange F := (f.comp L.subtype).codRestrict _
    (fun l => hlinear (Subgroup.mem_map_of_mem f l.property))
  let e := pGammaL2PGLRangeEquiv F
  let φ : L →* PGL2 F := e.symm.toMonoidHom.comp t
  have hφ (l : L) : f l = SemidirectProduct.inl (φ l) :=
    (congrArg Subtype.val (e.apply_symm_apply (t l))).symm
  refine ⟨φ, hφ, ?_⟩
  ext l
  change φ l = 1 ↔ f l = 1
  rw [hφ]
  constructor
  · intro h
    rw [h, map_one]
  · intro h
    exact SemidirectProduct.inl_injective (h.trans (map_one _).symm)

public theorem exists_pgl2_restriction_of_full_linear_layer
    {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (f : H →* PGammaL2 F)
    (L N : Subgroup H) (hNL : N ≤ L)
    (hlinear : L.map f ≤ pGammaL2PGLRange F)
    (hcore : N.map f = pGammaL2PSLRange F)
    (hindex : (f.ker ⊔ N).relIndex L = 2) :
    ∃ φ : L →* PGL2 F, Function.Surjective φ ∧
      (∀ l : L, f l = SemidirectProduct.inl (φ l)) ∧
      φ.ker = f.ker.subgroupOf L ∧
      (Matrix.ProjectiveSpecialLinearGroup.toPGL.range).comap φ =
        (f.ker ⊔ N).subgroupOf L := by
  let J := pGammaL2PSLRange F
  let P := pGammaL2PGLRange F
  have hpre : J.comap f = f.ker ⊔ N := by
    rw [show J = N.map f from hcore.symm, Subgroup.comap_map_eq, sup_comm]
  have hJI : J ≤ L.map f := by
    rw [show J = N.map f from hcore.symm]
    exact Subgroup.map_mono hNL
  have hJi : J.relIndex (L.map f) = 2 := by
    rw [← Subgroup.relIndex_comap, hpre]
    exact hindex
  have hIPi : (L.map f).relIndex P = 1 := by
    have hmul := Subgroup.relIndex_mul_relIndex J (L.map f) P hJI hlinear
    rw [hJi, pGammaL2_psl_range_relIndex_pgl_eq_two F hF] at hmul
    omega
  have himage : L.map f = P :=
    le_antisymm hlinear (Subgroup.relIndex_eq_one.mp hIPi)
  let t : L →* P := (f.comp L.subtype).codRestrict P
    (fun l => hlinear (Subgroup.mem_map_of_mem f l.property))
  have ht : Function.Surjective t := by
    intro y
    have hy : y.val ∈ L.map f := by rw [himage]; exact y.property
    obtain ⟨x, hx, he⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext he⟩
  let e := pGammaL2PGLRangeEquiv F
  let φ : L →* PGL2 F := e.symm.toMonoidHom.comp t
  have hφ (l : L) : f l = SemidirectProduct.inl (φ l) := by
    have he := congrArg Subtype.val (e.apply_symm_apply (t l))
    exact he.symm
  have hker : φ.ker = f.ker.subgroupOf L := by
    ext l
    change φ l = 1 ↔ f l = 1
    rw [hφ]
    constructor
    · intro h
      rw [h, map_one]
    · intro h
      exact SemidirectProduct.inl_injective (h.trans (map_one _).symm)
  have hφpre : (Matrix.ProjectiveSpecialLinearGroup.toPGL.range).comap φ =
      (f.ker ⊔ N).subgroupOf L := by
    ext l
    change φ l ∈ Matrix.ProjectiveSpecialLinearGroup.toPGL.range ↔ (l : H) ∈ f.ker ⊔ N
    rw [← hpre]
    change _ ↔ f l ∈ J
    rw [hφ]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, congrArg SemidirectProduct.inl ha⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, SemidirectProduct.inl_injective ha⟩
  exact ⟨φ, e.symm.surjective.comp ht, hφ, hker, hφpre⟩

end GorensteinWalter
