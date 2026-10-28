module

public import Theory.Representation.PSL3Two.SmallModules
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PPerfectHom
public import Theory.Representation.BinaryOffender.SectionLinear

/-!
# Residual-fixed margins in the binary SL₃ cover argument

A two-perfect group acting on a binary module with fixed displacements acts
trivially: its image has exponent two. In a cover of SL₃(2) with two-group
kernel, any subgroup with nontrivial quotient image normally generates modulo
the kernel. If that subgroup fixes the module, the two-residual does too.
These facts control nonsplit fixed margins in the composition argument for
Meierfrankenfeld–Stellmacher (1993), (1.4)–(1.5), pp.842–843.
-/

public section

open Representation Representation.BinaryOffender Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Triple.Composition
variable {G E : Type*} [Group G] [AddCommGroup E] [Module (ZMod 2) E]

/-- A binary action of a two-perfect group cannot have only fixed displacements. -/
theorem fixed_of_fixed_displacements (ρ : Representation (ZMod 2) G E)
    (K : Subgroup G) (hK : IsPPerfect 2 K)
    (h : ∀ g ∈ K, ∀ v, ρ g v - v ∈ fixedSpace ρ K) :
    fixedSpace ρ K = ⊤ := by
  let σ : Representation (ZMod 2) K E := ρ.comp K.subtype
  let f := σ.asGroupHom
  have htwo (v : E) : v + v = 0 := by
    simpa only [two_smul] using (show (2 : ZMod 2) • v = 0 by rw [show (2 : ZMod 2) = 0 by decide, zero_smul])
  have hs (g : K) (v : E) : σ g (σ g v) = v := by
    have hh := h g g.property v g
    change σ g (σ g v - v) = σ g v - v at hh
    rw [map_sub] at hh
    calc
      _ = (σ g v - v) + σ g v := sub_eq_iff_eq_add.mp hh
      _ = (σ g v + σ g v) - v := by abel
      _ = v := by rw [htwo, zero_sub]; exact neg_eq_iff_add_eq_zero.mpr (htwo v)
  have hp : IsPGroup 2 f.range := by
    rintro ⟨_, g, rfl⟩
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro v
    exact hs g v
  have hf := hK.hom_eq_one_of_isPGroup hp f.rangeRestrict
  apply top_unique
  intro v _ g
  have he := congrArg (fun t => (t g).val.val v) hf
  exact he

/-- When the actor covers a nontrivial subgroup of the simple quotient,
trivial actor action forces the entire two-residual to act trivially. -/
theorem residual_fixed_of_actor_fixed (π : G →* BinaryLinearThree.Group)
    (hπ : Function.Surjective π) (hk : IsPGroup 2 π.ker)
    (A : Subgroup G) (hA : A.map π ≠ ⊥)
    (ρ : Representation (ZMod 2) G E) (hfix : fixedSpace ρ A = ⊤) :
    fixedSpace ρ (pResidual 2 G) = ⊤ := by
  let f := ρ.asGroupHom
  have hAK : A ≤ f.ker := by
    intro a ha
    apply Units.ext
    apply LinearMap.ext
    intro v
    exact (show v ∈ fixedSpace ρ A by rw [hfix]; trivial) ⟨a, ha⟩
  let : IsSimpleGroup BinaryLinearThree.Group := Atlas.Comparisons.Exceptional.sl3Two_simple
  let : (f.ker.map π).Normal := (inferInstance : f.ker.Normal).map π hπ
  have hmap : f.ker.map π = ⊤ := by
    rcases (inferInstance : (f.ker.map π).Normal).eq_bot_or_eq_top with hbot | htop
    · exact False.elim (hA (bot_unique (hbot ▸ Subgroup.map_mono hAK)))
    · exact htop
  have hrange : π.ker.map f = f.range := by
    apply le_antisymm (Subgroup.map_le_range _ _) _
    rintro _ ⟨g, rfl⟩
    obtain ⟨k, hk', he⟩ := Subgroup.mem_map.mp
      (show π g ∈ f.ker.map π by rw [hmap]; trivial)
    refine Subgroup.mem_map.mpr ⟨k⁻¹ * g, ?_, ?_⟩
    · simp only [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
    · simp only [map_mul, map_inv, MonoidHom.mem_ker.mp hk', inv_one, one_mul]
  have hp : IsPGroup 2 f.range := hrange ▸ hk.map f
  have hq : IsPGroup 2 (G ⧸ f.ker) :=
    hp.of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  have hr : pResidual 2 G ≤ f.ker := sInf_le ⟨inferInstance, hq⟩
  apply top_unique
  intro v _ g
  exact congrArg (fun t => t.val v) (MonoidHom.mem_ker.mp (hr g.property))
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Triple.Composition
