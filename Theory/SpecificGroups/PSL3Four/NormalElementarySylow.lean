module
public import Theory.SpecificGroups.PSL3Even.MinimalParabolicWitness.CentralActor
public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.ElementaryAbelian.Injective

/-!
# Normal elementary subgroups in a diagram-acting PSL₃(4) Sylow

Let an actual finite-group action on PSL₃(4) contain all inner automorphisms.
The image of its Sylow two-subgroup restricts to a Sylow subgroup of the
inner component. Mark that intersection as UT₃ by inner conjugacy. A normal
elementary subgroup intersects the component in an invariant elementary
subgroup; a diagram-swapping actor puts this intersection in the highest
root. Normality then gives central displacement on UT₃ for every elementary
actor. The proved coordinate calculation makes every such actor inner.

The image statement requires neither a faithful action nor a condition on
its kernel. The original-subgroup wrapper retains the literal homomorphism.
The nontrivial diagram action is an actual hypothesis of the source branch.

Source: Aschbacher–Smith, Lemma 14.2.13, printed p.984, nonabelian U paragraph;
the root-plane and central-displacement calculations are E.2.7, p.219.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups Pointwise
open Matrix.PSL3.LinearThree Matrix.PSL3.LinearThree.OuterExtensions
open Matrix.PSL3Even.UnipotentGeometry Matrix.PSL3Even.MinimalParabolicWitness
namespace Matrix.PSL3Four.NormalElementarySylow

private theorem centerless : center PSL = ⊥ := by
  let := Atlas.sl_perfect (F := F) 3 (by decide)
  exact Group.IsPerfect.center_quotient_center_eq_bot SL

private theorem conj_injective : Function.Injective (MulAut.conj : PSL →* MulAut PSL) :=
  MulAut.conj_injective_of_center_eq_bot centerless

private theorem conj_actor (a : MulAut PSL) (x : PSL) :
    MulAut.conj (a x) = a * MulAut.conj x * a⁻¹ := by
  ext y
  simp

private theorem comap_inner_invariant (E : Subgroup (MulAut PSL))
    (a : MulAut PSL) (ha : a ∈ normalizer (E : Set (MulAut PSL))) :
    (E.comap MulAut.conj).map a.toMonoidHom = E.comap MulAut.conj := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x,hx,rfl⟩
    change MulAut.conj (a x) ∈ E
    rw [conj_actor]
    exact (ha (MulAut.conj x)).mp hx
  · rw [Subgroup.card_map_of_injective a.injective]

private theorem standard_placement (T E : Subgroup (MulAut PSL))
    (hU : T.comap MulAut.conj = unipotent F)
    (hswap : ∃ a ∈ T, diagramAction F (n := 2) (by decide) (by simpa using card_F) a ≠ 1)
    [IsElementaryAbelian 2 E] (hET : E ≤ T)
    (hn : T ≤ normalizer (E : Set (MulAut PSL))) :
    E ≤ MulAut.innerSubgroup PSL := by
  let A := E.comap (MulAut.conj : PSL →* MulAut PSL)
  let r : A →* E := (MulAut.conj : PSL →* MulAut PSL).restrict (fun _ hx => hx)
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_injective r
    (by intro x y h; apply Subtype.ext; apply conj_injective; exact congrArg Subtype.val h)
  have hAU : A ≤ unipotent F := by rw [← hU]; exact comap_mono hET
  have hpres (a : MulAut PSL) (ha : a ∈ T) :
      (unipotent F).map a.toMonoidHom = unipotent F := by
    rw [← hU]
    exact comap_inner_invariant T a (T.le_normalizer ha)
  obtain ⟨a,ha,hs⟩ := hswap
  have hAZ : A ≤ projectiveCenter F := elementary_invariant_le_center F
    (n := 2) (by decide) (by simpa using card_F) a (hpres a ha) hs A hAU
      (comap_inner_invariant E a (hn ha))
  intro b hb
  apply inner_of_central_displacement F (n := 2) (by decide) (by simpa using card_F)
    b (hpres b (hET hb)) (elemPow_eq_one_of_isElementaryAbelian b hb)
  intro u hu
  apply hAZ
  change MulAut.conj (b u * u⁻¹) ∈ E
  rw [map_mul,map_inv,conj_actor]
  have huT : MulAut.conj u ∈ T := by
    change u ∈ T.comap MulAut.conj
    rwa [hU]
  have hh := (hn huT b⁻¹).mp (E.inv_mem hb)
  simpa only [mul_assoc] using E.mul_mem hb hh

private theorem sylow_inner_preimage
    {X : Type*} [Group X] [Finite X] (ρ : X →* MulAut PSL)
    (hinner : MulAut.innerSubgroup PSL ≤ ρ.range) (S : Sylow 2 X) :
    ∃ R : Sylow 2 PSL, (R : Subgroup PSL) = ((S : Subgroup X).map ρ).comap MulAut.conj := by
  let f : PSL →* ρ.range := MulAut.conj.codRestrict ρ.range
    (fun x => hinner ⟨x,rfl⟩)
  have hf : Function.Injective f := by
    intro x y h
    exact conj_injective (congrArg Subtype.val h)
  let K := (MulAut.innerSubgroup PSL).subgroupOf ρ.range
  have hfr : f.range = K := by
    ext a
    constructor
    · rintro ⟨x,rfl⟩; exact ⟨x,rfl⟩
    · rintro ⟨x,hx⟩
      exact ⟨x,Subtype.ext hx⟩
  let e : PSL ≃* K := (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hfr)
  let Q := S.mapSurjective ρ.rangeRestrict_surjective
  obtain ⟨P,hP⟩ := Q.exists_subgroupOf_eq_of_normal K
  let R := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  refine ⟨R, ?_⟩
  ext x
  change x ∈ (P : Subgroup K).map e.symm.toMonoidHom ↔ _
  rw [mem_map_equiv]
  change e x ∈ (P : Subgroup K) ↔ _
  rw [hP]
  change f x ∈ (S : Subgroup X).map ρ.rangeRestrict ↔ MulAut.conj x ∈ (S : Subgroup X).map ρ
  constructor
  · rintro ⟨y,hy,he⟩
    exact ⟨y,hy,congrArg Subtype.val he⟩
  · rintro ⟨y,hy,he⟩
    exact ⟨y,hy,Subtype.ext he⟩

/-- A normal elementary subgroup of the original Sylow has inner image as
soon as the image contains the component and the Sylow acts on its diagram.
The original action may have a kernel. -/
theorem normal_elementary_le_inner_of_sylow_image
    {X : Type*} [Group X] [Finite X] (ρ : X →* MulAut PSL)
    (hinner : MulAut.innerSubgroup PSL ≤ ρ.range) (S : Sylow 2 X)
    (A : Subgroup (MulAut PSL)) [IsElementaryAbelian 2 A]
    (hAT : A ≤ (S : Subgroup X).map ρ)
    (hn : (S : Subgroup X).map ρ ≤ normalizer (A : Set (MulAut PSL)))
    (hswap : ∃ t ∈ (S : Subgroup X),
      diagramAction F (n := 2) (by decide) (by simpa using card_F) (ρ t) ≠ 1) :
    A ≤ MulAut.innerSubgroup PSL := by
  let T₀ := (S : Subgroup X).map ρ
  obtain ⟨R,hR⟩ := sylow_inner_preimage ρ hinner S
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL R
    (unipotentSylow F (n := 2) (by decide) (by simpa using card_F))
  let γ : MulAut PSL := MulAut.conj g
  let c : MulAut (MulAut PSL) := MulAut.conj γ
  have hU : (T₀.map c.toMonoidHom).comap MulAut.conj = unipotent F := by
    have he : (T₀.map c.toMonoidHom).comap MulAut.conj =
        (T₀.comap MulAut.conj).map γ.toMonoidHom := by
      ext x
      simp only [mem_comap, mem_map_equiv]
      change γ⁻¹ * MulAut.conj x * (γ⁻¹)⁻¹ ∈ T₀ ↔ MulAut.conj (γ⁻¹ x) ∈ T₀
      rw [conj_actor]
    rw [he, ← hR]
    exact congrArg Sylow.toSubgroup hg
  have hswap' : ∃ a ∈ T₀.map c.toMonoidHom,
      diagramAction F (n := 2) (by decide) (by simpa using card_F) a ≠ 1 := by
    obtain ⟨t,ht,hs⟩ := hswap
    refine ⟨c (ρ t), mem_map_of_mem c.toMonoidHom (mem_map_of_mem ρ ht), ?_⟩
    intro he
    apply hs
    let δ := diagramAction F (n := 2) (by decide) (by simpa using card_F)
    change δ (γ * ρ t * γ⁻¹) = 1 at he
    rw [map_mul, map_mul, map_inv] at he
    exact (mul_inv_eq_one.mp he) |> fun h => mul_left_cancel (h.trans (mul_one (δ γ)).symm)
  let : IsElementaryAbelian 2 (A.map c.toMonoidHom) := IsElementaryAbelian.map c.toMonoidHom
  have hplaced : A.map c.toMonoidHom ≤ MulAut.innerSubgroup PSL :=
    standard_placement (T₀.map c.toMonoidHom) (A.map c.toMonoidHom) hU hswap'
      (map_mono hAT)
      ((map_mono hn).trans (A.le_normalizer_map c.toMonoidHom))
  intro a ha
  have hh := hplaced (mem_map_of_mem c.toMonoidHom ha)
  have hm := (MulAut.innerSubgroup_normal PSL).conj_mem _ hh γ⁻¹
  change γ⁻¹ * (γ * a * γ⁻¹) * (γ⁻¹)⁻¹ ∈ MulAut.innerSubgroup PSL at hm
  simpa only [inv_inv, ← mul_assoc, inv_mul_cancel, one_mul, inv_mul_cancel_right] using hm

/-- Literal transport of a normal elementary subgroup through an action with
arbitrary kernel. -/
theorem normal_elementary_image_le_inner
    {X : Type*} [Group X] [Finite X] (ρ : X →* MulAut PSL)
    (hinner : MulAut.innerSubgroup PSL ≤ ρ.range) (S : Sylow 2 X)
    (E : Subgroup X) [IsElementaryAbelian 2 E]
    (hES : E ≤ (S : Subgroup X))
    (hn : (S : Subgroup X) ≤ normalizer (E : Set X))
    (hswap : ∃ t ∈ (S : Subgroup X),
      diagramAction F (n := 2) (by decide) (by simpa using card_F) (ρ t) ≠ 1) :
    E.map ρ ≤ MulAut.innerSubgroup PSL := by
  let : IsElementaryAbelian 2 (E.map ρ) := IsElementaryAbelian.map ρ
  exact normal_elementary_le_inner_of_sylow_image ρ hinner S (E.map ρ)
    (map_mono hES) ((map_mono hn).trans (E.le_normalizer_map ρ)) hswap

end Matrix.PSL3Four.NormalElementarySylow

