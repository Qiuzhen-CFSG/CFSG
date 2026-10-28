module

public import CFSG.Quasithin.ChapterD.Section03.SourceSetup
public import Theory.GroupTheory.ComponentLocalOrbitCore
public import Theory.Representation.BinaryOffender.RatioInheritance

/-!
# The seed actor kernel in the D.3 source setup

The seed `I` is stabilized by the prescribed two-local subgroup.  After
restricting to that stabilizer, the component orbit is still the original
orbit (via the literal subgroup-of map).  The component normal dichotomy then
shows that the kernel of the restricted action centralizes the orbit.  This
isolates the faithful actor input used by the later D.3 module alternatives;
it does not assert any of those alternatives.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.ChapterD.Section03
universe u v
variable {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {κ : GroupClass.{u}}
    {T : Sylow 2 G} {X L : Subgroup G} {I : Submodule (ZMod 2) V}

private theorem kernel_centralizes_orbit {D E : Type*} [Group D] [Group E]
    (f : D →* E) (K S : Subgroup D) (hK : IsComponent D K)
    (hn : ¬ componentOrbit K S ≤ f.ker) :
    f.ker ≤ centralizer (componentOrbit K S : Set D) := by
  rcases hK.normal_dichotomy f.ker with hk | hk
  · exact (hn (iSup_conjugates_le_of_le_normalizer K S f.ker hk
      (by rw [normalizer_eq_top]; exact le_top))).elim
  · apply le_centralizer_iff.mp
    exact iSup_conjugates_le_centralizer K S f.ker
      (by rw [normalizer_eq_top]; exact le_top) hk

omit [Finite G] in
private theorem orbit_subgroupOf (P K S : Subgroup G) (hKP : K ≤ P) (hSP : S ≤ P) :
    componentOrbit (K.subgroupOf P) (S.subgroupOf P) =
      (componentOrbit K S).subgroupOf P := by
  apply map_injective P.subtype_injective
  rw [map_componentOrbit,map_subgroupOf_eq_of_le hKP,map_subgroupOf_eq_of_le hSP,
    map_subgroupOf_eq_of_le]
  exact iSup_conjugates_le_of_le_normalizer K S P hKP (hSP.trans P.le_normalizer)

/-- The kernel of the action on the seed centralizes its actual component orbit. -/
theorem SourceHypotheses.stable_seed_kernel_centralizes
    (h : SourceHypotheses κ ρ T X I) (hL : IsComponent G L)
    (hX : X = componentOrbit L (T : Subgroup G))
    (hT : (T : Subgroup G) ≤ subspaceStabilizer ρ I) :
    subspaceKernel ρ I ⊤ ≤ centralizer (X : Set G) := by
  let P := subspaceStabilizer ρ I
  let f := subspaceActionHom ρ I
  have hXP : X ≤ P := h.seed.choose
  have hLP : L ≤ P := (hX ▸ le_componentOrbit L (T : Subgroup G)).trans hXP
  have ho : componentOrbit (L.subgroupOf P) ((T : Subgroup G).subgroupOf P) =
      X.subgroupOf P := by rw [orbit_subgroupOf P L T hLP hT,←hX]
  have hn : ¬ componentOrbit (L.subgroupOf P) ((T : Subgroup G).subgroupOf P) ≤ f.ker := by
    rw [ho]
    intro hall
    apply h.seed.not_le_fixedSpace ρ
    intro v hv x
    have he := hall (show (⟨x,hXP x.property⟩ : P) ∈ X.subgroupOf P from x.property)
    have he' := congrArg (fun a => subspaceImageRepresentation ρ I a ⟨v,hv⟩) he
    exact congrArg (fun w : I => (w : V)) he'
  have hc := kernel_centralizes_orbit f (L.subgroupOf P)
    ((T : Subgroup G).subgroupOf P) (hL.subgroupOf hLP) hn
  rw [ho] at hc
  have hNP : subspaceKernel ρ I ⊤ ≤ P := by
    change subspaceKernel ρ I ⊤ ≤ subspaceStabilizer ρ I
    apply le_subspaceStabilizer ρ I
    intro n hn v hv
    rw [hn.2 v hv]
    exact hv
  intro n hn x hx
  let a : P := ⟨n,hNP hn⟩
  have ha : a ∈ f.ker := by
    apply MonoidHom.mem_ker.mpr
    apply subspaceImageRepresentation_injective ρ I
    ext w
    exact hn.2 w w.property
  exact congrArg Subtype.val (hc ha ⟨x,hXP hx⟩ hx)

/-- A subgroup disjoint from the seed centralizer acts faithfully on the seed image. -/
theorem SourceHypotheses.stable_seed_actor_injective
    (h : SourceHypotheses κ ρ T X I) (hL : IsComponent G L)
    (hX : X = componentOrbit L (T : Subgroup G))
    (hT : (T : Subgroup G) ≤ subspaceStabilizer ρ I)
    (A : Subgroup G) (hAT : A ≤ (T : Subgroup G))
    (hfaith : A ⊓ centralizer (X : Set G) = ⊥) :
    Function.Injective (subgroupActionHom ρ I A (hAT.trans hT)) := by
  apply (subgroupActionHom_injective_iff ρ I A (hAT.trans hT)).mpr
  apply bot_unique
  intro a ha
  exact hfaith.le ⟨ha.1,h.stable_seed_kernel_centralizes hL hX hT ⟨mem_top _,ha.2⟩⟩

end CFSG.Quasithin.ChapterD.Section03
