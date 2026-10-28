module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.NaturalIndex
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootImage

/-!
# Quadratic actors on the full replacement moving layer

The literal embedding transports a vanishing double group commutator to
quadratic action on the cover. Its natural quotient has isotropic
displacement of dimension at most two. Exact fixed-index preservation for
the full central cover then bounds the original centralizer index by q².
The acting group is the whole inner vertex quotient at the original degree;
no central fixed subgroup is removed or assumed trivial.

The Thompson actor in `RootProduct` consumes this bound to become a genuine
small mover in MS93 (5.0)--(5.1), pp.912--913.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Representation.SymplecticFourOrthogonalCover
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit

private theorem embedded_quadratic
    {G D W : Type*} [Group G] [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (V A : Subgroup G) (σ : Representation (ZMod 2) D W)
    (j : Multiplicative W →* G) (hj : Function.Injective j) (hjr : j.range = V)
    (f : A →* D)
    (hact : ∀ (x : A) (w : W), j (Multiplicative.ofAdd (σ (f x) w)) =
      x.val*j (Multiplicative.ofAdd w)*x.val⁻¹)
    (hq : ⁅⁅V,A⁆,A⁆ = ⊥) :
    ∀ x ∈ f.range, ∀ y ∈ f.range, ∀ w : W,
      σ x (σ y w-w) = σ y w-w := by
  rintro x ⟨x,rfl⟩ y ⟨y,rfl⟩ w
  have hjw : j (Multiplicative.ofAdd w) ∈ V := hjr ▸ (show _ ∈ j.range from ⟨_,rfl⟩)
  have hd : j (Multiplicative.ofAdd (σ (f y) w-w)) = ⁅y.val,j (Multiplicative.ofAdd w)⁆ := by
    rw [ofAdd_sub,div_eq_mul_inv,map_mul,map_inv,hact]
    rfl
  have hm : ⁅y.val,j (Multiplicative.ofAdd w)⁆ ∈ ⁅V,A⁆ := by
    rw [commutator_comm V A]
    exact commutator_mem_commutator y.property hjw
  have hc := (commutator_eq_bot_iff_le_centralizer.mp hq) hm x.val x.property
  apply Multiplicative.ofAdd.injective
  apply hj
  rw [hact,hd,hc,mul_inv_cancel_right]

private theorem binary_natural_quadratic_index
    {E : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (L (K := E)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := E))) (hp : IsCover p)
    (A : Subgroup (L (K := E)))
    (hq : ∀ x ∈ A, ∀ y ∈ A, ∀ w, σ x (σ y w-w)=σ y w-w) :
    2 ^ fixedCodim σ A ≤ Nat.card E ^ 2 := by
  let ed : L (K := E) →* Sp E := (commutator (Sp E)).subtype
  have hquad : ∀ x ∈ A.map ed, ∀ y ∈ A.map ed, ∀ v : Vector E,
      x • (y • v-v)=y • v-v := by
    rintro x ⟨x,hx,rfl⟩ y ⟨y,hy,rfl⟩ v
    obtain ⟨w,rfl⟩ := hp.1 v
    have he := congrArg p (hq x hx y hy w)
    have hpy : p (σ y w-w) = binaryNatural y (p w)-p w := by
      rw [map_sub,p.isIntertwining]
    rw [p.isIntertwining,hpy] at he
    exact he
  have hdim := TwoLocalCover.finrank_le_two_of_isotropic (displacementSpace (A.map ed))
    (quadratic_displacement_isotropic _ hquad)
  rw [fixedCodim_of_binaryCover p hp]
  let τ := restrictScalars (k := ZMod 2) (symplecticNatural (k := E) 2)
  have hfixed : fixedSpace (binaryNatural (K := E)) A =
      (TwoLocalCover.fixedSpace (A.map ed)).restrictScalars (ZMod 2) := by
    ext v
    constructor
    · intro hv x hx
      obtain ⟨y,hy,rfl⟩ := hx
      exact hv ⟨y,hy⟩
    · intro hv x
      exact hv (ed x.val) (mem_map_of_mem ed x.property)
  have hi : 2 ^ fixedCodim (binaryNatural (K := E)) A =
      Nat.card (Vector E ⧸ TwoLocalCover.fixedSpace (A.map ed)) := by
    change 2 ^ Module.finrank (ZMod 2) (Vector E ⧸ fixedSpace (binaryNatural (K := E)) A) = _
    rw [hfixed]
    have hc := Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv (ZMod 2)
      (TwoLocalCover.fixedSpace (A.map ed))).toEquiv
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hc
    exact hc
  rw [hi,fixed_quotient_card]
  exact Nat.pow_le_pow_right Nat.card_pos hdim

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Quadraticity on the entire original moving layer bounds its exact
centralizer index by q², retaining the fixed kernel of the cover. -/
theorem Input.replacement_quadratic_moving_index_le_square
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a : Vertex d.radical} (ha : color d.radical a = false)
    (A : Subgroup (FreeAmalgam d.radical)) (hAS : A ≤ stabilizer d.radical a)
    (hquad : ⁅⁅U d.radical a,A⁆,A⁆ = ⊥) :
    (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) ≤ Nat.card F ^ 2 := by
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C := (K.subgroupOf d.overgroup).map q
  let : C.Normal := (h.replacement_component_image_structure d).2.1
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 d.overgroup)) := omegaCenterIn_elementary _
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d ha
  have hCtop : C = ⊤ := by
    have hpre : C.comap q = ⊤ := by
      rw [show C = (K.subgroupOf d.overgroup).map q from rfl,
        comap_map_eq,QuotientGroup.ker_mk']
      exact h.replacement_inner_of_four_le d geometry hb
    rw [←map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) C,hpre]
    rw [←MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  let κC := κ.codRestrict C (fun x => hCtop ▸ mem_top (κ x))
  let f := (e.groupEquiv.toMonoidHom.comp κC).comp (inclusion hAS)
  let σ := MovedSection.coverAction s e
  have hact (x : A) w : j (Multiplicative.ofAdd (σ (f x) w)) =
      x.val*j (Multiplicative.ofAdd w)*x.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC (inclusion hAS x)))) w)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj (inclusion hAS x) w
  have hi := embedded_centralizer_index σ (U d.radical a) A j hj hjr f hact
  have hq := embedded_quadratic (U d.radical a) A σ j hj hjr f hact hquad
  have hbound := binary_natural_quadratic_index σ (MovedSection.coverProjection s e) he f.range hq
  rw [E.card_eq,hE,←h.field_card] at hbound
  exact hi.trans_le hbound

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
