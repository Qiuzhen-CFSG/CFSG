module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.OuterGeneration.Action

/-!
# Lifting the outer conjugate generators to the source group

The actual semilinear action is faithful on L⟨t⟩ for an outer involution t.
Indeed each element of that extension is in L or Lt, and the second coset
cannot map into the inner subgroup. Generation by conjugates whose conjugators
lie in the marked PSL₂ therefore lifts through the original L-isomorphism.
This retains conjugators in G without assuming that G itself embeds in Aut(L).

Source: the four-conjugate step of Guralnick--Malle, Classification of
2F-modules I, Proposition 4.1, manuscript pp.8--9; Aschbacher--Smith K.2,
printed p.453. The concrete model generators remain an explicit input.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.OuterGeneration
open Subgroup Representation GorensteinWalter

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

private lemma injective_on_extension {G K : Type*} [Group G] [Finite G] [Group K]
    (L : Subgroup G) [L.Normal] (f : G →* K)
    (hfL : Function.Injective (f.comp L.subtype))
    (t : G) (ht : t ^ 2 = 1) (hout : f t ∉ L.map f) :
    Function.Injective (f.comp (L ⊔ zpowers t).subtype) := by
  classical
  have htne : t ≠ 1 := by
    intro he
    apply hout
    rw [he, map_one]
    exact one_mem _
  apply (f.comp (L ⊔ zpowers t).subtype).ker_eq_bot_iff.mp
  apply le_bot_iff.mp
  intro x hx
  have hfx : f (x : G) = 1 := hx
  obtain ⟨l, hl, z, hz, he⟩ := mem_sup_of_normal_left.mp x.property
  have hz' := mem_zpowers_iff_mem_range_orderOf.mp hz
  rw [orderOf_eq_prime ht htne] at hz'
  simp only [show Finset.range 2 = {0, 1} by decide, Finset.image_insert,
    Finset.image_singleton, pow_zero, pow_one, Finset.mem_insert,
    Finset.mem_singleton] at hz'
  apply Subtype.ext
  rcases hz' with hz1 | hz2
  · subst z
    have he' : l = (x : G) := by simpa using he
    have hh : f.comp L.subtype ⟨l, hl⟩ = f.comp L.subtype 1 := by
      simpa only [MonoidHom.comp_apply, Subgroup.coe_mk, map_one] using he' ▸ hfx
    have h1 := congrArg Subtype.val (hfL hh)
    exact he'.symm.trans h1
  · rw [hz2] at he
    exfalso
    apply hout
    have hh : f t = f l⁻¹ := by
      have hp : f l * f t = 1 := by rw [← map_mul, he]; exact hfx
      simpa only [map_inv] using eq_inv_of_mul_eq_one_right hp
    exact hh ▸ mem_map.mpr ⟨l⁻¹, L.inv_mem hl, rfl⟩

private lemma lift_conjugate_generators {G K : Type*} [Group G] [Finite G] [Group K]
    (L : Subgroup G) [L.Normal] (f : G →* K)
    (hfL : Function.Injective (f.comp L.subtype))
    (t : G) (ht : t ^ 2 = 1) (hout : f t ∉ L.map f)
    {n : ℕ} (c : Fin n → L)
    (hgen : L.map f ≤ Subgroup.closure (Set.range fun i => f (c i) * f t * (f (c i))⁻¹)) :
    L ≤ Subgroup.closure (Set.range fun i => (c i : G) * t * (c i : G)⁻¹) := by
  let H := closure (Set.range fun i => (c i : G) * t * (c i : G)⁻¹)
  let M := L ⊔ zpowers t
  have hHM : H ≤ M := by
    apply (Subgroup.closure_le (K := M)).mpr
    rintro _ ⟨i, rfl⟩
    exact M.mul_mem (M.mul_mem ((le_sup_left : L ≤ M) (c i).property)
      ((le_sup_right : zpowers t ≤ M) (mem_zpowers t))) (M.inv_mem ((le_sup_left : L ≤ M) (c i).property))
  have hmap : H.map f = closure (Set.range fun i => f (c i) * f t * (f (c i))⁻¹) := by
    change (closure (Set.range fun i => (c i : G) * t * (c i : G)⁻¹)).map f = _
    rw [MonoidHom.map_closure]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, by simp⟩
    · rintro ⟨i, rfl⟩
      exact ⟨(c i : G) * t * (c i : G)⁻¹, ⟨i, rfl⟩, by simp⟩
  have hi := injective_on_extension L f hfL t ht hout
  intro l hl
  obtain ⟨x, hx, hxl⟩ := mem_map.mp (hmap ▸ hgen (mem_map.mpr ⟨l, hl, rfl⟩))
  have he : (⟨x, hHM hx⟩ : M) = ⟨l, (le_sup_left : L ≤ M) hl⟩ := hi hxl
  have hxl' : x = l := congrArg Subtype.val he
  change l ∈ H
  exact hxl' ▸ hx

lemma lift_semilinear_generators [Finite G] {F : Type*} [Field F] [Finite F]
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [L.Normal]
    [IsIrreducible (ρ.comp L.subtype)] (hf : Function.Injective ρ)
    (eL : L ≃* PSL2 F) (hF : IsOddPrimePower (Nat.card F))
    (hlarge : 3 < Nat.card F) {t : G} (ht : t ^ 2 = 1) (hout : t ∉ L)
    {n : ℕ} (c : Fin n → PSL2 F)
    (hgen : pGammaL2PSLRange F ≤ Subgroup.closure (Set.range fun i =>
      SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL (c i)) *
        semilinearAction L eL hF hlarge t *
          (SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL (c i)))⁻¹)) :
    ∃ g : Fin n → G, L ≤ Subgroup.closure (Set.range fun i => g i * t * (g i)⁻¹) := by
  let f := semilinearAction L eL hF hlarge
  have himage := semilinearAction_map_component L eL hF hlarge
  have htout : f t ∉ L.map f := by
    rw [himage]
    exact fun hh => hout ((involution_mem_inner_iff ρ L hf eL hF hlarge ht).mp hh)
  refine ⟨fun i => (eL.symm (c i) : G), ?_⟩
  apply lift_conjugate_generators L f (semilinearAction_component_injective L eL hF hlarge)
    t ht htout (fun i => eL.symm (c i))
  simpa only [f, himage, semilinearAction_coe, MulEquiv.apply_symm_apply] using hgen

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.OuterGeneration
