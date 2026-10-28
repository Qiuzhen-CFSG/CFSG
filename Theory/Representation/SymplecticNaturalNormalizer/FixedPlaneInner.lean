module
public import Theory.SpecificGroups.SymplecticFour.FixedPlaneDisplacement
public import Theory.Representation.SymplecticNaturalNormalizer.FixedLineInner

/-!
# Inner actors fixing a symplectic plane

Symplectic operators fixing a self-orthogonal plane commute: each displacement
lies in that plane and hence is fixed by the other operator. For a centric
normal natural component, fixing one entire nonzero field line removes the
outer field twist, so all ambient plane fixers lie in the component. Applying
these facts to a marked embedded cover gives inner containment and commuting
images through the original quotient, retaining its exact kernel.

Source: MS93 (3.3), first symplectic paragraph, printed p.867.
-/

public section
open Subgroup Representation
open Theory.SpecificGroups.SymplecticFour
namespace SymplecticNaturalNormalizer
variable {F : Type*} [Field F]

theorem commute_of_fixes_self_orthogonal
    (P : Submodule F (Vector F)) (hP : (form F).orthogonal P = P)
    (g h : Sp F) (hg : ∀ v ∈ P, g • v = v) (hh : ∀ v ∈ P, h • v = v) :
    Commute g h := by
  have hv (v : Vector F) : (g*h) • v = (h*g) • v := by
    have hg' := hg _ (displacement_mem_of_self_orthogonal P hP h hh v)
    have hh' := hh _ (displacement_mem_of_self_orthogonal P hP g hg v)
    rw [smul_sub] at hg' hh'
    simp only [mul_smul]
    calc
      g • (h • v) = (h • v-v)+g • v := sub_eq_iff_eq_add.mp hg'
      _ = (g • v-v)+h • v := by abel
      _ = h • (g • v) := (sub_eq_iff_eq_add.mp hh').symm
  change g*h=h*g
  apply Subtype.ext
  apply Matrix.ext
  intro i k
  simpa [smul_eq_mulVec,Matrix.mulVec_single] using congrFun (hv (Pi.single k 1)) i

variable [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

theorem mem_component_of_fixes_self_orthogonal
    {G : Type*} [Group G] (B : Subgroup G) [B.Normal]
    (hcent : centralizer (B : Set G) ≤ B)
    (hcard : 2 < Nat.card F) (e : B ≃* Sp F)
    (ρ : Representation (ZMod 2) G (Vector F))
    (hB : ∀ b : B, ∀ w, ρ (b:G) w = symplecticNatural 2 (e b) w)
    (P : Submodule F (Vector F)) (hP : (form F).orthogonal P=P)
    (x : G) (hfix : ∀ v ∈ P, ρ x v=v) : x ∈ B := by
  have hne : P ≠ ⊥ := by
    intro he
    rw [he,LinearMap.BilinForm.orthogonal_bot] at hP
    exact top_ne_bot hP
  obtain ⟨v,hv,hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact mem_component_of_fixes_field_line B hcent hcard e ρ hB x v hvne
    (fun c => hfix _ (P.smul_mem c hv))

theorem commute_of_ambient_plane_fixers
    {G : Type*} [Group G] (B : Subgroup G) [B.Normal]
    (hcent : centralizer (B : Set G) ≤ B)
    (hcard : 2 < Nat.card F) (e : B ≃* Sp F)
    (ρ : Representation (ZMod 2) G (Vector F))
    (hB : ∀ b : B, ∀ w, ρ (b:G) w = symplecticNatural 2 (e b) w)
    (P : Submodule F (Vector F)) (hP : (form F).orthogonal P=P)
    (x y : G) (hx : ∀ v ∈ P, ρ x v=v) (hy : ∀ v ∈ P, ρ y v=v) :
    Commute x y := by
  let xB : B := ⟨x,mem_component_of_fixes_self_orthogonal B hcent hcard e ρ hB P hP x hx⟩
  let yB : B := ⟨y,mem_component_of_fixes_self_orthogonal B hcent hcard e ρ hB P hP y hy⟩
  have hh := commute_of_fixes_self_orthogonal P hP (e xB) (e yB)
    (fun v hv => (hB xB v).symm.trans (hx v hv))
    (fun v hv => (hB yB v).symm.trans (hy v hv))
  have hh' : xB*yB=yB*xB := e.injective (by simpa only [map_mul] using hh.eq)
  exact congrArg Subtype.val hh'


open scoped commutatorElement

theorem centralizer_plane_lifts_inner_and_commutes
    {G J V : Type*} [Group G] [Group J]
    [AddCommGroup V] [Module (ZMod 2) V]
    (S K C A Y D : Subgroup G) (hAS : A ≤ S) (hYS : Y ≤ S)
    (q : S →* J) (B : Subgroup J) [B.Normal]
    (hKB : (K.subgroupOf S).map q = B) (hker : q.ker.map S.subtype = C)
    (hcent : centralizer (B : Set J) ≤ B)
    (hcard : 2 < Nat.card F) (e : B ≃* Sp F)
    (ρ : Representation (ZMod 2) J (Vector F))
    (hB : ∀ b : B, ∀ w, ρ (b:J) w = symplecticNatural 2 (e b) w)
    (σ : Representation (ZMod 2) J V)
    (j : Multiplicative V →* G) (hj : Function.Injective j)
    (hact : ∀ (g : S) (w : V), j (Multiplicative.ofAdd (σ (q g) w)) =
      (g:G)*j (Multiplicative.ofAdd w)*(g:G)⁻¹)
    (p : V →ₗ[ZMod 2] Vector F)
    (hproj : ∀ g w, p (σ g w) = ρ g (p w))
    (P : Submodule F (Vector F)) (hP : (form F).orthogonal P=P)
    (hcover : ∀ v ∈ P, ∃ w : V, j (Multiplicative.ofAdd w) ∈ D ∧ p w=v)
    (hA : ∀ a : A, ∀ v ∈ P, ρ (q ⟨a,hAS a.property⟩) v=v)
    (hc : Y ≤ centralizer (D : Set G)) :
    Y ≤ K ⊔ C ∧ ⁅A,Y⁆ ≤ C := by
  have hY (y : Y) : ∀ v ∈ P, ρ (q ⟨y,hYS y.property⟩) v=v := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := hcover v hv
    have hs : σ (q ⟨y,hYS y.property⟩) w=w := by
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [hact,←hc y.property _ hw,mul_inv_cancel_right]
    rw [←hproj,hs]
  constructor
  · intro y hy
    have hb := mem_component_of_fixes_self_orthogonal B hcent hcard e ρ hB P hP
      (q ⟨y,hYS hy⟩) (hY ⟨y,hy⟩)
    rw [←hKB] at hb
    obtain ⟨k,hk,hqk⟩ := hb
    let z : S := k⁻¹*⟨y,hYS hy⟩
    have hz : z ∈ q.ker := by
      change q z=1
      simp only [z,map_mul,map_inv,hqk,inv_mul_cancel]
    have hzc : (z:G) ∈ C := hker ▸ mem_map_of_mem S.subtype hz
    have hh := (K ⊔ C).mul_mem (mem_sup_left hk) (mem_sup_right hzc)
    simpa only [z,coe_mul,coe_inv,subtype_apply,mul_inv_cancel_left] using hh
  · have hh : ⁅A.subgroupOf S,Y.subgroupOf S⁆ ≤ q.ker := by
      apply commutator_le.mpr
      intro a ha y hy
      change q ⁅a,y⁆=1
      rw [map_commutatorElement]
      apply commutatorElement_eq_one_iff_commute.mpr
      exact commute_of_ambient_plane_fixers B hcent hcard e ρ hB P hP (q a) (q y)
        (hA ⟨a,ha⟩) (hY ⟨y,hy⟩)
    have hm := map_mono (f := S.subtype) hh
    rwa [map_commutator,map_subgroupOf_eq_of_le hAS,map_subgroupOf_eq_of_le hYS,hker] at hm

end SymplecticNaturalNormalizer
