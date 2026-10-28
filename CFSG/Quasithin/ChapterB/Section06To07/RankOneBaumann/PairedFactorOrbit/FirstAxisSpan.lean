module
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedFactorOrbit.NaturalAxis
public import Theory.Representation.BinaryOffender.PPerfectFixedLift
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
public import Theory.GroupTheory.ConjugateSpanOrder
/-!
# The first moved support lies in the actual alpha orbit

Lift the natural first Sylow fixed line into the original Thompson-fixed
subgroup. A conjugator in the same first factor residual gives the second
line. Their sum covers the first support; the remaining discrepancy lies
in the original fixed kernel, already in the seed. No splitting is used.
Source: Aschbacher–Smith B.6.10/E.2.3, pp.117 and216–217.
-/
public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterB.RankOneBaumann.PairedFactorOrbit
open QuasisimpleSource
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
variable (F : BinaryField)
local notation "D" => Matrix.SpecialLinearGroup (Fin 2) F.Carrier
local notation "V" => Fin 2 → F.Carrier
local notation "N" => linearNatural F 2

omit [Finite G] [Finite H] in
theorem first_axis_moved_le_orbit
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (J E K : Subgroup G)
    (hJE : U ⊓ centralizer (J : Set G) ≤ E)
    (f : Additive U →ₗ[ZMod 2] (V × V)) (hf : Function.Surjective f)
    (j : D →* H)
    (himage : K.map q = (pResidual 2 D).map j)
    (he : ∀ g v, f (NormalElementaryQuotient.representation U q hq hker (j g) v) =
      (N g (f v).1,(f v).2))
    (P Q : Sylow 2 D)
    (hfix : fixedSpace (NormalElementaryQuotient.representation U q hq hker) (J.map q) =
      ((fixedSpace N (P : Subgroup D)).prod (fixedSpace N (Q : Subgroup D))).comap f) :
    (⁅U,K⁆ : Subgroup G) ≤ conjugateSpanBy E K := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let M := subspaceCommutator α ⊤ (K.map q)
  have hm : M.map f = (⊤ : Submodule (ZMod 2) V).prod ⊥ := by
    dsimp [M]
    rw [himage]
    exact first_axis_moved_map F α j f hf he
  have hfixed (v : Additive U)
      (hv : f v ∈ (fixedSpace N (P : Subgroup D)).prod (fixedSpace N (Q : Subgroup D))) :
      (v.toMul : G) ∈ E := by
    have hh : v ∈ fixedSpace α (J.map q) := hfix.ge hv
    exact hJE ⟨v.toMul.property,(NormalElementaryQuotient.mem_fixedSpace_image U q hq hker J v).mp hh⟩
  obtain ⟨g,hg,hspan⟩ := exists_residual_fixed_line_span F P
  obtain ⟨a,ha,haq⟩ := himage.ge (mem_map_of_mem j hg)
  let O := conjugateSpanBy E K
  let W : Submodule (ZMod 2) (Additive U) :=
    AddSubgroup.toZModSubmodule 2 ((O ⊓ U).subgroupOf U).toAddSubgroup
  have heW (v : Additive U) (hv : (v.toMul:G) ∈ E) : v ∈ W := ⟨le_conjugateSpanBy E K hv,v.toMul.property⟩
  have hfirst (v : Additive U) (hv : (f v).2 = 0) : v ∈ W := by
    have hvs : (f v).1 ∈ fixedSpace N (P : Subgroup D) ⊔
        (fixedSpace N (P : Subgroup D)).map (N g) := hspan.symm ▸ Submodule.mem_top
    obtain ⟨u,hu,w',⟨w,hw,rfl⟩,huw⟩ := Submodule.mem_sup.mp hvs
    obtain ⟨x,hx⟩ := hf (u,0)
    obtain ⟨y,hy⟩ := hf (w,0)
    have hxE : (x.toMul:G) ∈ E := hfixed x (by rw [hx]; exact ⟨hu,Submodule.zero_mem _⟩)
    have hyE : (y.toMul:G) ∈ E := hfixed y (by rw [hy]; exact ⟨hw,Submodule.zero_mem _⟩)
    have hay : α (q a) y ∈ W := by
      change ((α (q a) y).toMul : G) ∈ (O ⊓ U : Subgroup G)
      refine ⟨?_,(α (q a) y).toMul.property⟩
      rw [NormalElementaryQuotient.representation_apply]
      exact subset_closure ⟨a,ha,y.toMul,hyE,rfl⟩
    have hz : f (v - x - α (q a) y) = 0 := by
      rw [map_sub,map_sub,haq,he,hx,hy]
      apply Prod.ext
      · change (f v).1 - u - N g w = 0
        rw [←huw]
        abel
      · change (f v).2 - 0 - 0 = 0
        simp only [hv,sub_zero]
    have hzW : v - x - α (q a) y ∈ W := heW _ (hfixed _ (by rw [hz]; exact Submodule.zero_mem _))
    have hh := W.add_mem (W.add_mem hzW (heW x hxE)) hay
    convert hh using 1
    abel
  have hMO : (⁅U,K⁆ : Subgroup G) ≤ O := by
    intro x hx
    let v : Additive U := Additive.ofMul ⟨x,(commutator_le_left U K) hx⟩
    have hvM : v ∈ M := by
      change v ∈ subspaceCommutator α ⊤ (K.map q)
      rw [←NormalElementaryQuotient.commutatorSpace_eq U q hq hker]
      exact hx
    have hv : (f v).2 = 0 := (hm.le (Submodule.mem_map_of_mem hvM)).2
    exact (hfirst v hv).1
  exact hMO
end CFSG.Quasithin.ChapterB.RankOneBaumann.PairedFactorOrbit
