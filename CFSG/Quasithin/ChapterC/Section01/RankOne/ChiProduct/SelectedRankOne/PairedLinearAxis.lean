module
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedFactorOrbit.NaturalAxis
public import Theory.Representation.BinaryOffender.PPerfectFixedLift
public import Theory.Representation.BinaryOffender.PerfectMoved
/-!
# Natural coordinates on the original first support

A two-perfect opposite actor fixes the entire preimage of the first natural
support across the original central kernel. The first coordinate therefore
gives the exact action kernel and natural fixed kernel on the first moved
module, without choosing a complement.

Source: Aschbacher–Smith B.6.10 and C.1.26, printed pp.117 and132.
-/
public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB.QuasisimpleSource ChapterB.RankOneBaumann.PairedFactorOrbit
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
variable (F : BinaryField)
local notation "D" => Matrix.SpecialLinearGroup (Fin 2) F.Carrier
local notation "W" => Fin 2 → F.Carrier

theorem opposite_axis_fixes_first_preimage
    (ρ : Representation (ZMod 2) G V) (j : D × D →* G)
    (hD : IsPPerfect 2 D)
    (f : V →ₗ[ZMod 2] (W × W))
    (hk : f.ker ≤ fixedSpace ρ j.range)
    (he : ∀ g v, f (ρ (j g) v) =
      (linearNatural F 2 g.1 (f v).1,linearNatural F 2 g.2 (f v).2))
    (v : V) (hv : (f v).2 = 0) (a : D) : ρ (j (1,a)) v = v := by
  let j₂ := j.comp (MonoidHom.inr D D)
  have htop : IsPPerfect 2 (⊤ : Subgroup D) := hD.of_surjective (topEquiv (G := D)).symm.toMonoidHom (topEquiv (G := D)).symm.surjective
  have hh := fixed_of_pPerfect_central_kernel (ρ.comp j₂) (⊤ : Subgroup D) htop f
    (fun w hw b => hk hw ⟨j (1,(b:D)),⟨(1,(b:D)),rfl⟩⟩) v ?_
  · exact hh ⟨a,mem_top a⟩
  · intro b
    change f (ρ (j (1,(b:D))) v) = f v
    rw [he,hv,map_one,Module.End.one_apply,map_zero]
    exact Prod.ext rfl hv.symm

theorem first_axis_projection_kernel
    (ρ : Representation (ZMod 2) G V) (j : D × D →* G)
    (f : V →ₗ[ZMod 2] (W × W))
    (hk : f.ker ≤ fixedSpace ρ j.range)
    (he : ∀ g v, f (ρ (j g) v) =
      (linearNatural F 2 g.1 (f v).1,linearNatural F 2 g.2 (f v).2))
    (v : V) (hv : (f v).2 = 0) :
    (f v).1 = 0 ↔ ∀ a : D, ρ (j (a,1)) v = v := by
  constructor
  · intro h a
    exact hk (show v ∈ f.ker from Prod.ext h hv) ⟨j (a,1),⟨(a,1),rfl⟩⟩
  · intro h
    have hfix : (f v).1 ∈ fixedSpace (linearNatural F 2) ⊤ := by
      intro a
      have hh := congrArg (fun x => (f x).1) (h a)
      rw [he] at hh
      exact hh
    apply (ExtensionConsequences.linearNatural_invariants F (by decide)).le
    exact fun g => hfix ⟨g,mem_top _⟩

theorem first_axis_action_kernel
    (ρ : Representation (ZMod 2) G V) (j : D × D →* G)
    (hD : IsPPerfect 2 D)
    (f : V →ₗ[ZMod 2] (W × W))
    (hk : f.ker ≤ fixedSpace ρ j.range)
    (he : ∀ g v, f (ρ (j g) v) =
      (linearNatural F 2 g.1 (f v).1,linearNatural F 2 g.2 (f v).2))
    (M : Submodule (ZMod 2) V)
    (hm : M.map f = (⊤ : Submodule (ZMod 2) W).prod ⊥)
    (g : D × D) :
    (∀ v ∈ M, ρ (j g) v = v) ↔ g.1 = 1 := by
  constructor
  · intro h
    have hg : linearNatural F 2 g.1 = 1 := by
      apply LinearMap.ext
      intro w
      obtain ⟨v,hv,hfv⟩ := hm.ge (show (w,0) ∈ (⊤ : Submodule (ZMod 2) W).prod ⊥ from
        ⟨Submodule.mem_top,Submodule.zero_mem _⟩)
      have hh := congrArg (fun x => (f x).1) (h v hv)
      rw [he,hfv] at hh
      exact hh
    apply Subtype.ext
    apply Matrix.ext_iff_mulVec.mpr
    intro w
    change (g.1.val).mulVec w = (1 : Matrix (Fin 2) (Fin 2) F.Carrier).mulVec w
    rw [Matrix.one_mulVec]
    exact LinearMap.congr_fun hg w
  · intro hg v hv
    have hsecond : (f v).2 = 0 := (hm.le (Submodule.mem_map_of_mem hv)).2
    have hh := opposite_axis_fixes_first_preimage F ρ j hD f hk he v hsecond g.2
    simpa only [←hg,Prod.mk.eta] using hh

theorem first_axis_projection_surjective
    (f : V →ₗ[ZMod 2] (W × W)) (M : Submodule (ZMod 2) V)
    (hm : M.map f = (⊤ : Submodule (ZMod 2) W).prod ⊥) :
    Function.Surjective ((LinearMap.fst (ZMod 2) W W).comp (f.comp M.subtype)) := by
  intro w
  obtain ⟨v,hv,hfv⟩ := hm.ge (show (w,0) ∈ (⊤ : Submodule (ZMod 2) W).prod ⊥ from
    ⟨Submodule.mem_top,Submodule.zero_mem _⟩)
  exact ⟨⟨v,hv⟩,congrArg Prod.fst hfv⟩
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
