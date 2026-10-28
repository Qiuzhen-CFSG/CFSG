module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.Assembly
public import Theory.GroupTheory.PCoreResidualFrattiniKernel
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.ReducedNormal.Basic

/-!
# The actual reduced module of an irreducible primary radical

Let X be two-perfect and normalized by a Sylow two-subgroup T. If T
acts irreducibly on X/O₂,Φ(X), every noncentral action of X on R₂(XT)
has kernel in O₂,Φ(X). The two-residual of XT is exactly X. The residual
Frattini kernel theorem therefore identifies C_T(R₂(XT)) with O₂(XT).
There is no exponent-p hypothesis and no assertion that X belongs to Ξ.
Source: Aschbacher--Smith 3.2.14, p.585.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter3.RadicalCentralization
open Chapter1
variable {G : Type*} [Group G] [Finite G]

/-- Irreducibility of the original radical action bounds the literal
kernel on the reduced subgroup of its join with T. -/
theorem reduced_kernel_le_frattini (T X : Subgroup G)
    (hT : T ≤ normalizer (X : Set G))
    (hi : ∀ A : Subgroup (XiFrattiniQuotient X),
      (∀ t a, a ∈ A → xiFrattiniAction T X hT t a ∈ A) → A = ⊥ ∨ A = ⊤)
    (hne : ⁅reducedTwoSubgroup (X ⊔ T : Subgroup G), X.subgroupOf (X ⊔ T)⁆ ≠ ⊥) :
    (centralizer (reducedTwoSubgroup (X ⊔ T : Subgroup G) :
      Set (X ⊔ T : Subgroup G))).comap (inclusion (show X ≤ X ⊔ T from le_sup_left)) ≤
      (frattini (XiQuotient X)).comap (QuotientGroup.mk' (pCore 2 X)) := by
  let J := X ⊔ T
  let W := reducedTwoSubgroup J
  let C := centralizer (W : Set J)
  let i : X →* J := inclusion (show X ≤ J from le_sup_left)
  let K := C.comap i
  let q := QuotientGroup.mk' (pCore 2 X)
  let r := QuotientGroup.mk' (frattini (XiQuotient X))
  let f := r.comp q
  let := conjMulDistribMulActionOfLeNormalizer T X hT
  have hK : ∀ t : T, ∀ x ∈ K, (t • x : X) ∈ K := by
    intro t x hx
    exact (inferInstance : C.Normal).conj_mem (i x) hx
      (⟨t, (show T ≤ J from le_sup_right) t.property⟩ : J)
  have hstable : ∀ t : T, ∀ y ∈ K.map f,
      xiFrattiniAction T X hT t y ∈ K.map f := by
    rintro t y ⟨x,hx,rfl⟩
    refine ⟨t • x,hK t x hx,?_⟩
    simp only [f,r,q,xiFrattiniAction,MonoidHom.comp_apply,quotientAut_apply_mk]
    rfl
  rcases hi (K.map f) (fun t y hy => hstable t y hy) with hb | ht
  · intro x hx
    change q x ∈ frattini (XiQuotient X)
    apply (QuotientGroup.eq_one_iff (q x)).mp
    exact (show f x = 1 from mem_bot.mp (hb ▸ mem_map_of_mem f hx))
  · have hqK : K.map q = ⊤ := by
      apply frattini_nongenerating
      have hh := congrArg (Subgroup.comap r) ht
      rw [← Subgroup.map_map] at hh
      simpa only [comap_map_eq,r,QuotientGroup.ker_mk',comap_top] using hh
    have hcore : pCore 2 X ≤ K := by
      intro x hx
      have hh := pCoreIn_mono_of_normalizes (show X ≤ J from le_sup_left)
        (sup_le X.le_normalizer hT) (mem_map_of_mem X.subtype hx)
      obtain ⟨y,hy,he⟩ := hh
      have hey : y = i x := Subtype.ext he
      exact le_centralizer_iff.mp (reducedPSubgroup_le_centralizer_pCore 2 J) (hey ▸ hy)
    have hKtop : K = ⊤ := by
      have hh := congrArg (Subgroup.comap q) hqK
      simpa only [comap_map_eq,q,QuotientGroup.ker_mk',comap_top,
        sup_of_le_left hcore] using hh
    apply False.elim
    apply hne
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mp
    intro x hx
    exact (show (⟨x.val,hx⟩ : X) ∈ K from hKtop.symm ▸ mem_top _)

/-- The literal core--Frattini kernel condition identifies the Sylow
centralizer without an odd-quotient shape or a Ξ-membership premise. -/
theorem reduced_sylow_centralizer_of_frattini (T : Sylow 2 G) (X : Subgroup G)
    (hT : (T : Subgroup G) ≤ normalizer (X : Set G)) (hX : IsPPerfect 2 X)
    (hker : (centralizer (reducedTwoSubgroup (X ⊔ (T : Subgroup G) : Subgroup G) :
      Set (X ⊔ (T : Subgroup G) : Subgroup G))).comap
        (inclusion (show X ≤ X ⊔ (T : Subgroup G) from le_sup_left)) ≤
      (frattini (XiQuotient X)).comap (QuotientGroup.mk' (pCore 2 X))) :
    (T : Subgroup G).subgroupOf (X ⊔ (T : Subgroup G)) ⊓
      centralizer (reducedTwoSubgroup (X ⊔ (T : Subgroup G) : Subgroup G) :
        Set (X ⊔ (T : Subgroup G) : Subgroup G)) =
      pCore 2 (X ⊔ (T : Subgroup G) : Subgroup G) := by
  let J := X ⊔ (T : Subgroup G)
  let Y := X.subgroupOf J
  let S := (T : Subgroup G).subgroupOf J
  let C := centralizer (reducedTwoSubgroup J : Set J)
  let : Y.Normal := normal_subgroupOf_of_le_normalizer (sup_le X.le_normalizer hT)
  let e : Y ≃* X := subgroupOfEquivOfLe (show X ≤ J from le_sup_left)
  have hY : IsPPerfect 2 Y := hX.of_surjective e.symm.toMonoidHom e.symm.surjective
  have hgen : Y ⊔ S = ⊤ := by
    rw [← subgroupOf_sup (show X ≤ J from le_sup_left)
      (show (T : Subgroup G) ≤ J from le_sup_right)]
    exact subgroupOf_self _
  have hres : pResidual 2 J = Y :=
    pResidual_eq_of_isPPerfect_sup Y S hY T.isPGroup'.comap_subtype hgen
  let f := QuotientGroup.mk' C
  have hk : pResidual 2 J ⊓ f.ker ≤
      ((frattini ((pResidual 2 J) ⧸ pCore 2 (pResidual 2 J))).comap
        (QuotientGroup.mk' (pCore 2 (pResidual 2 J)))).map (pResidual 2 J).subtype := by
    rw [hres]
    have heker : IsPGroup 2 e.toMonoidHom.ker := by
      rw [(MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective]
      exact IsPGroup.of_card (n := 0) (by simp)
    have he := e.toMonoidHom.comap_frattini_pCore_of_pKernel e.surjective heker
    rintro y ⟨hy,hc⟩
    refine ⟨⟨y,hy⟩,?_,rfl⟩
    rw [← he]
    exact hker ((QuotientGroup.eq_one_iff y).mp hc)
  have hkill : pCore 2 J ≤ f.ker := by
    rw [QuotientGroup.ker_mk']
    exact le_centralizer_iff.mp (reducedPSubgroup_le_centralizer_pCore 2 J)
  simpa only [f,QuotientGroup.ker_mk',Sylow.coe_subtype] using
    f.sylow_inf_ker_eq_pCore_of_residual_frattini_kernel
    (QuotientGroup.mk'_surjective C) (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right))
    hkill hk

/-- A nontrivial original primary action constructs the entire reduced
module/Sylow-centralizer input used in the guarded ratio theorem. -/
theorem reduced_sylow_centralizer (T : Sylow 2 G) (X : Subgroup G)
    (hT : (T : Subgroup G) ≤ normalizer (X : Set G)) (hX : IsPPerfect 2 X)
    (hi : ∀ A : Subgroup (XiFrattiniQuotient X),
      (∀ t a, a ∈ A → xiFrattiniAction (T : Subgroup G) X hT t a ∈ A) → A = ⊥ ∨ A = ⊤)
    (hne : ⁅reducedTwoSubgroup (X ⊔ (T : Subgroup G) : Subgroup G),
      X.subgroupOf (X ⊔ (T : Subgroup G))⁆ ≠ ⊥) :
    (T : Subgroup G).subgroupOf (X ⊔ (T : Subgroup G)) ⊓
      centralizer (reducedTwoSubgroup (X ⊔ (T : Subgroup G) : Subgroup G) :
        Set (X ⊔ (T : Subgroup G) : Subgroup G)) =
      pCore 2 (X ⊔ (T : Subgroup G) : Subgroup G) :=
  reduced_sylow_centralizer_of_frattini T X hT hX
    (reduced_kernel_le_frattini (T : Subgroup G) X hT hi hne)

end CFSG.Quasithin.Chapter3.RadicalCentralization
