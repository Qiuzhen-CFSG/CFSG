module
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedFactorOrbit.NaturalAxis
public import Theory.Representation.BinaryOffender.PPerfectFixedLift
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
public import Theory.GroupTheory.ConjugateSpanOrder
/-!
# Alpha splits against one actual moved support

The first-support part lifts from the actual moved space. Its remaining
quotient coordinate lies in the opposite support, and the two-perfect
fixed-lift lemma proves that the first residual fixes it. This derives
alpha ≤ [U,K] C_alpha(K) without splitting U over its central kernel.
Source: Aschbacher–Smith B.6.10, printed p.117.
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
theorem first_factor_alpha_le_commutator_fixed
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (J E R K : Subgroup G) (hKR : K ≤ R) (hK : IsPPerfect 2 K)
    (hE : E = (E ⊓ centralizer (R : Set G)) ⊔ (U ⊓ centralizer (J : Set G)))
    (f : Additive U →ₗ[ZMod 2] (V × V)) (hf : Function.Surjective f)
    (j : D →* H)
    (himage : K.map q = (pResidual 2 D).map j)
    (he : ∀ g v, f (NormalElementaryQuotient.representation U q hq hker (j g) v) =
      (N g (f v).1,(f v).2))
    (hk : f.ker ≤ fixedSpace (NormalElementaryQuotient.representation U q hq hker) (K.map q))
    (P Q : Sylow 2 D)
    (hfix : fixedSpace (NormalElementaryQuotient.representation U q hq hker) (J.map q) =
      ((fixedSpace N (P : Subgroup D)).prod (fixedSpace N (Q : Subgroup D))).comap f) :
    E ≤ (⁅U,K⁆ : Subgroup G) ⊔ (E ⊓ centralizer (K : Set G)) := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let M := subspaceCommutator α ⊤ (K.map q)
  have hm : M.map f = (⊤ : Submodule (ZMod 2) V).prod ⊥ := by
    dsimp [M]
    rw [himage]
    exact first_axis_moved_map F α j f hf he
  have hjE : U ⊓ centralizer (J : Set G) ≤ E := le_sup_right.trans hE.ge
  have hfixed (v : Additive U)
      (hv : f v ∈ (fixedSpace N (P : Subgroup D)).prod (fixedSpace N (Q : Subgroup D))) :
      (v.toMul : G) ∈ E := by
    have hh : v ∈ fixedSpace α (J.map q) := hfix.ge hv
    exact hjE ⟨v.toMul.property,(NormalElementaryQuotient.mem_fixedSpace_image U q hq hker J v).mp hh⟩
  have hcross (v : Additive U) (hv : (f v).1 = 0) :
      (v.toMul : G) ∈ centralizer (K : Set G) := by
    apply (NormalElementaryQuotient.mem_fixedSpace_image U q hq hker K v).mp
    have hh := fixed_of_pPerfect_central_kernel (α.comp q) K hK f
      (fun w hw a => hk hw ⟨q a,mem_map_of_mem q a.property⟩) v ?_
    · intro a
      obtain ⟨k,hk',hka⟩ := a.property
      change α a v = v
      rw [←hka]
      exact hh ⟨k,hk'⟩
    · intro a
      obtain ⟨g,hg,hga⟩ := himage.le (mem_map_of_mem q a.property)
      change f (α (q a) v) = f v
      rw [←hga,he,hv,map_zero]
      exact Prod.ext hv.symm rfl
  have hEle : E ≤ (⁅U,K⁆ : Subgroup G) ⊔ (E ⊓ centralizer (K : Set G)) := by
    nth_rw 1 [hE]
    apply sup_le
    · exact (inf_le_inf_left E (centralizer_le hKR)).trans le_sup_right
    · intro x hx
      let v : Additive U := Additive.ofMul ⟨x,hx.1⟩
      have hvfix : f v ∈ (fixedSpace N (P : Subgroup D)).prod (fixedSpace N (Q : Subgroup D)) :=
        hfix.le ((NormalElementaryQuotient.mem_fixedSpace_image U q hq hker J v).mpr hx.2)
      have hvm : ((f v).1,0) ∈ M.map f := hm.ge ⟨Submodule.mem_top,Submodule.zero_mem _⟩
      obtain ⟨m,hmM,hfm⟩ := hvm
      have hmE : (m.toMul:G) ∈ E := hfixed m (by rw [hfm]; exact ⟨hvfix.1,Submodule.zero_mem _⟩)
      have hvc : (f (v-m)).1 = 0 := by rw [map_sub,hfm]; exact sub_self _
      have hvcE : ((v-m).toMul:G) ∈ E := by
        rw [toMul_sub,div_eq_mul_inv]
        exact E.mul_mem (hjE hx) (E.inv_mem hmE)
      have hmcomm : (m.toMul:G) ∈ (⁅U,K⁆ : Subgroup G) := by
        change m ∈ NormalElementaryQuotient.commutatorSpace U K
        rw [NormalElementaryQuotient.commutatorSpace_eq U q hq hker]
        exact hmM
      have hh := mul_mem_sup hmcomm (show ((v-m).toMul:G) ∈ E ⊓ centralizer (K : Set G) from ⟨hvcE,hcross _ hvc⟩)
      have heq : (m.toMul:G) * ((v-m).toMul:G) = x := by
        change ((m+(v-m)).toMul:G) = x
        rw [show m+(v-m)=v by abel]
        rfl
      exact heq ▸ hh
  exact hEle
end CFSG.Quasithin.ChapterB.RankOneBaumann.PairedFactorOrbit
