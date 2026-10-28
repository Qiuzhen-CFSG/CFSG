module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource.CoreSetup
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.ResidualIncidence.Generation
public import Theory.AtlasPort.LinearGroups.G2.CubicCartan
public import Theory.GroupTheory.PResidual.NormalizedSupplement

/-!
# The original G₂ Cartan and its two residual factors

One original quotient map and one conjugating element align the full flag.
On the model Borel, the point and plane characters are l and lm in the
split-torus parameters (l,m). Their kernels are respectively the long and
short residuals. The two-character map on the original odd Cartan is
injective because its full kernel is a two-group, and the known Cartan order
makes it surjective. Oddness lifts both character kernels into the actual
residuals, since O₂(L) normalizes them. Thus X splits as
(X ∩ L₁)(X ∩ L₂) with trivial intersection, retaining every central layer.

Source: Aschbacher--Smith 11.1.2, printed pp.762--763, combined manuscript,
1 March 2004. The octonion model calculations reuse the licensed ATLAS
port through its existing imports; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff. Source point L₁ is the code's long local₂;
source plane L₂ is the code's short local₁.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource.G2Cartan
open Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.SplitOctonion

private def shear (F : Type*) [Field F] : (Fˣ × Fˣ) ≃* (Fˣ × Fˣ) where
  toFun p := (p.1,p.1*p.2)
  invFun p := (p.1,p.1⁻¹*p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  map_mul' p q := by ext <;> simp [mul_comm,mul_left_comm]

private theorem torus_short {F : Type*} [Field F] [CharP F 2] (l m : Fˣ) :
    torus l m ∈ local₁ (F := F) ↔ l*m = 1 := by
  constructor
  · intro ht
    rw [local₁_eq_shortSpecial] at ht
    obtain ⟨g,hg,he⟩ := ht
    have he' : g.val = torus l m := he
    have hg' : (shortRepresentation g).det = 1 := hg
    have hrep : shortRepresentation g = !![(l : F),0;0,(m : F)] := by
      ext i j
      change g.val.val (basisVector (j.castLE (by decide : 2 ≤ 8)))
        (i.castLE (by decide : 2 ≤ 8)) = _
      rw [he']
      fin_cases i <;> fin_cases j <;>
        simp [torus,torusEquiv,torusLinear,torusWeights,basisVector]
    rw [hrep,Matrix.det_fin_two] at hg'
    exact Units.ext (by simpa using hg')
  · intro h
    have hm : m = l⁻¹ := eq_inv_iff_mul_eq_one.mpr (by simpa only [mul_comm] using h)
    rw [hm]
    exact short_torus_mem_local₁ l

private theorem torus_long {F : Type*} [Field F] [CharP F 2] (l m : Fˣ) :
    torus l m ∈ local₂ (F := F) ↔ l = 1 := by
  rw [local₂_eq_fixingFirstVector]
  change (torus l m).val (basisVector 0) = basisVector 0 ↔ l = 1
  rw [torus_first_basis]
  constructor
  · intro h
    apply Units.ext
    have hh := congrFun h 0
    simpa [basisVector] using hh
  · rintro rfl
    simp

private theorem model_character {F : Type*} [Field F] [CharP F 2]
    (i : Fin 2) (g : Atlas.G2.borel (K := F)) :
    (if i = 0 then (shear F (EvenBorelTorus.projection g)).1
      else (shear F (EvenBorelTorus.projection g)).2) = 1 ↔
      g.val ∈ G2.ResidualIncidence.standardLocal F i := by
  obtain ⟨⟨u,t⟩,he⟩ := (borelProductEquiv (K := F)).surjective g
  obtain ⟨p,hp⟩ := t.property
  have ht : torusHom p = t.val := hp
  let u' : Atlas.G2.borel (K := F) := ⟨u,mem_sup_left u.property⟩
  let t' : Atlas.G2.borel (K := F) := ⟨torusHom p,mem_sup_right ⟨p,rfl⟩⟩
  have hg : g = u'*t' := Subtype.ext (by
    change g.val = u.val * torusHom p
    rw [ht]
    exact (congrArg Subtype.val he).symm)
  have hz : EvenBorelTorus.projection u' = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [EvenBorelTorus.projection_ker]
    exact u.property
  have hc : EvenBorelTorus.projection g = p := by
    rw [hg,map_mul,hz,one_mul]
    exact EvenBorelTorus.projection_torus p
  have hul : u.val ∈ G2.ResidualIncidence.standardLocal F i := by
    fin_cases i
    · exact unipotent_le_local₂ u.property
    · exact unipotent_le_local₁ u.property
  rw [hc,hg]
  change _ ↔ u.val * torusHom p ∈ G2.ResidualIncidence.standardLocal F i
  rw [(G2.ResidualIncidence.standardLocal F i).mul_mem_cancel_left hul]
  fin_cases i
  · exact (torus_long p.1 p.2).symm
  · exact (torus_short p.1 p.2).symm

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))

private abbrev c := G2.coordinates S m
private abbrev f := G2.flag S m
private abbrev a := MulAut.conj (G2.ResidualIncidence.alignment S m).val
private abbrev r : L →* Atlas.G2.Model S.field.Carrier :=
  (a S m).symm.toMonoidHom.comp (c S m).quotientMap

private theorem r_ker : (r S m).ker = pCore 2 L := by
  ext x
  change (a S m).symm ((c S m).groupEquiv (QuotientGroup.mk' (pCore 2 L) x)) = 1 ↔ _
  rw [(a S m).symm.map_eq_one_iff,(c S m).groupEquiv.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff x

private theorem residual_image (i : Fin 2) :
    (((f S m).Li i).subgroupOf L).map (r S m) =
      G2.ResidualIncidence.standardLocal S.field.Carrier i := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    have hh := (G2.ResidualIncidence.localProjection S m i ⟨y,hy⟩).property
    rw [G2.ResidualIncidence.localProjection_coe] at hh
    exact hh
  · intro hx
    obtain ⟨y,hy⟩ := G2.ResidualIncidence.localProjection_surjective S m i ⟨x,hx⟩
    refine ⟨⟨y,(localResidual_le _ y.property).1⟩,y.property,?_⟩
    have hh := congrArg Subtype.val hy
    rw [G2.ResidualIncidence.localProjection_coe] at hh
    exact hh

private theorem cartan_borel {X : Subgroup G} (hX : IsCartan T L X) (x : X) :
    r S m ⟨x,(hX.1 x.property).1⟩ ∈ Atlas.G2.borel := by
  have hn (i : Fin 2) : (c S m).quotientMap ⟨x,(hX.1 x.property).1⟩ ∈
      (c S m).modelStabilizer ((f S m).space i.castSucc) :=
    ((c S m).mem_normalizer_preimage_iff _ _).mp
      ((f S m).cartan_normalizes (G2.flag_inner_unique S m) hX i.castSucc x.property)
  have hh (i : Fin 2) : r S m ⟨x,(hX.1 x.property).1⟩ ∈
      G2.ResidualIncidence.standardParabolic S.field.Carrier i := by
    have h := hn i
    rw [G2.ResidualIncidence.modelStabilizer_flag,mem_map_equiv] at h
    exact h
  exact parabolics_intersection.le ⟨hh 1,hh 0⟩

private def projection {X : Subgroup G} (hX : IsCartan T L X) :
    X →* Atlas.G2.borel (K := S.field.Carrier) :=
  ((r S m).comp (inclusion (hX.1.trans inf_le_left))).codRestrict _
    (cartan_borel S m hX)

private def characters {X : Subgroup G} (hX : IsCartan T L X) :
    X →* (S.field.Carrierˣ × S.field.Carrierˣ) :=
  (shear S.field.Carrier).toMonoidHom.comp
    (EvenBorelTorus.projection.comp (projection S m hX))

private theorem characters_injective {X : Subgroup G} (hX : IsCartan T L X) :
    Function.Injective (characters S m hX) := by
  have hk : IsPGroup 2 (projection S m hX).ker := by
    rw [projection,MonoidHom.ker_codRestrict]
    change IsPGroup 2 ((r S m).ker.comap (inclusion (hX.1.trans inf_le_left)))
    rw [r_ker]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  have hc : IsPGroup 2 (characters S m hX).ker := by
    rw [characters,MonoidHom.ker_comp_of_injective _ _ (shear S.field.Carrier).injective]
    change IsPGroup 2 (EvenBorelTorus.projection.ker.comap (projection S m hX))
    rw [EvenBorelTorus.projection_ker]
    exact EvenBorelTorus.radical_isTwoGroup.comap_of_ker_isPGroup _ hk
  exact (MonoidHom.ker_eq_bot_iff _).mp
    (card_eq_one.mp (hc.card_eq_or_dvd.resolve_right
      (hX.odd.of_dvd_nat (card_subgroup_dvd_card _)).not_two_dvd_nat))

private theorem characters_membership {X : Subgroup G} (hX : IsCartan T L X)
    (i : Fin 2) (x : X) :
    (if i = 0 then (characters S m hX x).1 else (characters S m hX x).2) = 1 ↔
      (x : G) ∈ (f S m).Li i := by
  change (if i = 0 then (shear S.field.Carrier (EvenBorelTorus.projection
    (projection S m hX x))).1 else (shear S.field.Carrier (EvenBorelTorus.projection
    (projection S m hX x))).2) = 1 ↔ _
  rw [model_character]
  let R := ((f S m).Li i).subgroupOf L
  let U := X.subgroupOf L ⊓ (R.map (r S m)).comap (r S m)
  have ho : Odd (Nat.card U) := by
    apply Odd.of_dvd_nat _ (card_dvd_of_le (show U ≤ X.subgroupOf L from inf_le_left))
    rw [Nat.card_congr (subgroupOfEquivOfLe (hX.1.trans inf_le_left)).toEquiv]
    exact hX.odd
  have hp : IsPPerfect 2 U := by
    intro N hn htwo
    let := hn
    apply index_eq_one.mp
    change Nat.card (U ⧸ N) = 1
    exact htwo.card_eq_or_dvd.resolve_right (fun hd =>
      ho.not_two_dvd_nat (hd.trans N.card_quotient_dvd_card))
  have hn : (r S m).ker ≤ normalizer (R : Set L) := by
    rw [r_ker,←subgroupOf_normalizer_eq
      (show (f S m).Li i ≤ L from (localResidual_le _).trans inf_le_left)]
    have hp : pCore 2 L ≤ (T : Subgroup G).subgroupOf L := by
      rw [←(c S m).innerSylow_coe]
      exact pCore_isPGroup.le_sylow_of_normal _
    exact hp.trans (comap_mono ((f S m).sylow_normalizes_Li i))
  have hUR : U ≤ R := le_of_isPPerfect_of_le_sup_of_normalizes U R _ hp
    (by rw [r_ker]; exact pCore_isPGroup) hn
    (by simpa only [U,comap_map_eq] using (inf_le_right : U ≤ _))
  constructor
  · intro hx
    change (⟨x,(hX.1 x.property).1⟩ : L) ∈ R
    apply hUR
    refine ⟨x.property,?_⟩
    change r S m ⟨x,(hX.1 x.property).1⟩ ∈ R.map _
    rw [residual_image]
    exact hx
  · intro hx
    have h := mem_map_of_mem (r S m) (show (⟨x,(hX.1 x.property).1⟩ : L) ∈ R from hx)
    rw [residual_image] at h
    exact h

/-- The two original G₂ residual intersections split the full Cartan, in source order. -/
theorem cartan_split {X : Subgroup G} (hX : IsCartan T L X)
    (f' : InvariantFlag (.g2 m)) :
    (X ⊓ f'.Li 0) ⊔ (X ⊓ f'.Li 1) = X ∧ Disjoint (X ⊓ f'.Li 0) (X ⊓ f'.Li 1) := by
  have hc : Nat.card X = Nat.card (S.field.Carrierˣ × S.field.Carrierˣ) := by
    rw [(c S m).cartan_card hX,Nat.card_prod,Nat.card_units,S.field.card_eq,pow_two]
  let := Fintype.ofFinite X
  let := Fintype.ofFinite (S.field.Carrierˣ × S.field.Carrierˣ)
  have hb : Function.Bijective (characters S m hX) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨characters_injective S m hX,by simpa only [Nat.card_eq_fintype_card] using hc⟩
  let e := MulEquiv.ofBijective (characters S m hX) hb
  have hf (i : Fin 2) : f'.Li i = (f S m).Li i := by
    change localResidual L ((c S m).preimage (f'.space i.castSucc)) = _
    rw [G2.flag_inner_unique S m i.castSucc (f'.space i.castSucc)
      (f'.dimension i.castSucc) (inf_le_left.trans (f'.invariant i.castSucc))]
    rfl
  have h₀ (x : X) : (e x).1 = 1 ↔ (x : G) ∈ f'.Li 0 := by
    rw [hf 0]
    exact characters_membership S m hX 0 x
  have h₁ (x : X) : (e x).2 = 1 ↔ (x : G) ∈ f'.Li 1 := by
    rw [hf 1]
    exact characters_membership S m hX 1 x
  constructor
  · apply le_antisymm (sup_le inf_le_left inf_le_left)
    intro x hx
    let a := e.symm (1,(e ⟨x,hx⟩).2)
    let b := e.symm ((e ⟨x,hx⟩).1,1)
    have ha : (a : G) ∈ X ⊓ f'.Li 0 := ⟨a.property,(h₀ a).mp (by simp [a])⟩
    have hb : (b : G) ∈ X ⊓ f'.Li 1 := ⟨b.property,(h₁ b).mp (by simp [b])⟩
    have hab : (a : G) * b = x := by
      change ((a*b : X) : G) = x
      have he : a*b = ⟨x,hx⟩ := e.injective (by simp [a,b])
      exact congrArg Subtype.val he
    rw [←hab]
    exact mul_mem_sup ha hb
  · apply disjoint_def.mpr
    intro x hx hy
    have he : e ⟨x,hx.1⟩ = 1 := Prod.ext ((h₀ _).mpr hx.2) ((h₁ _).mpr hy.2)
    exact congrArg Subtype.val (e.map_eq_one_iff.mp he)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource.G2Cartan
