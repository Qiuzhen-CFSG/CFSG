module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2CompletionGeometry
import all Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage.FrameAlignment.WeylCorrection
import all Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage.FrameAlignment.RankOneNormalizers

/-!
# The canonical Weyl product and the actual G₂ torus

Both compatible parabolic embeddings transport the native split torus to
the same subgroup of the whole overlap. Their Weyl involutions act on its
coordinates by (l,m) ↦ (m,l) and (l,m) ↦ (l,l/m). The product therefore
has an action of exact order six, including over F₄; its cube inverts the
torus and its sixth power centralizes it. Consequently six divides the
order of the actual ambient product.

If this sixth power belongs to the torus, it is both fixed and inverted
by the cube, hence is trivial in characteristic two. In particular, a
full ambient torus-centralizer bound discharges the canonical Weyl relation
and feeds the existing concrete completion recognition. That bound remains
a source obligation. No ambient recognition, exhaustive amalgam comparison
or original uniqueness conclusion is assumed or asserted unconditionally.

The source and Chapter12 applications retain the original maps and define
the torus using the literal whole-overlap isomorphism. The internal imports
reuse the native torus/Weyl identities and separating-unit calculation;
they preserve those implementation modules' public boundaries. Coordinate
formulas use the existing ATLAS port with LICENSES/ATLAS.txt attribution.

Source: Aschbacher–Smith F.4.8, F.4.26 and 5.3.3–4, printed pp.278,288,659
(`refs/quasithin.pdf`). This is a torus-action reduction of the remaining
completion recognition, not a proof of the full cited source theorems.
-/

open Subgroup Theory.GroupTheory Atlas.G2 Atlas.G2.LieParabolicSetup
open Atlas.G2.LieAutomorphismExtensions.InnerFieldCoverage
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2CompletionGeometry
variable {F : Type} [Field F]

private def nativeTorus₁ : (Fˣ × Fˣ) →* parabolic₁ (F := F) :=
  torusHom.codRestrict _ (fun p => borel_le_parabolic₁ (mem_sup_right ⟨p,rfl⟩))
private def nativeTorus₂ : (Fˣ × Fˣ) →* parabolic₂ (F := F) :=
  torusHom.codRestrict _ (fun p => borel_le_parabolic₂ (mem_sup_right ⟨p,rfl⟩))

/-- The order-six action induced by the canonical Weyl product on torus coordinates. -/
def torusRotation : MulAut (Fˣ × Fˣ) where
  toFun p := (p.1*p.2⁻¹,p.1)
  invFun p := (p.2,p.2*p.1⁻¹)
  left_inv p := by apply Prod.ext <;> simp
  right_inv p := by apply Prod.ext <;> simp [mul_left_comm]
  map_mul' p q := by apply Prod.ext <;> simp [mul_assoc,mul_comm,mul_left_comm]

theorem torusRotation_cube (p : Fˣ × Fˣ) :
    (torusRotation (F := F)^3) p=p⁻¹ := by
  change (p.1*p.2⁻¹*p.1⁻¹*(p.1*p.2⁻¹)⁻¹,p.1*p.2⁻¹*p.1⁻¹)=(p.1⁻¹,p.2⁻¹)
  apply Prod.ext <;> dsimp <;> simp [mul_assoc,mul_comm,mul_left_comm]

theorem torusRotation_order [Finite F] [CharP F 2] (hq : 2<Nat.card F) :
    orderOf (torusRotation (F := F))=6 := by
  obtain ⟨a,ha,hai⟩ := exists_separating_unit hq
  have h6 : (torusRotation (F := F))^6=1 := by
    apply MulEquiv.ext
    intro p
    rw [show 6=3*2 from rfl,pow_mul]
    change (torusRotation^3) ((torusRotation^3) p)=p
    rw [torusRotation_cube,torusRotation_cube,inv_inv]
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide) h6
  intro p hp hd hh
  have hp' : p=2 ∨ p=3 := by
    have hle := Nat.le_of_dvd (by decide : 0<6) hd
    interval_cases p <;> norm_num at *
  rcases hp' with rfl|rfl
  · have he := congrArg (fun f : MulAut (Fˣ × Fˣ) => f (a,1)) hh
    change (torusRotation^3) (a,1)=(a,1) at he
    rw [torusRotation_cube] at he
    exact hai (congrArg Prod.fst he).symm
  · have he := congrArg (fun f : MulAut (Fˣ × Fˣ) => (f (a,1)).1) hh
    exact ha (by simpa [torusRotation,pow_two] using he.symm)

namespace Completion
variable {G : Type*} [Group G] (c : Completion F G)

def torusMap : (Fˣ × Fˣ) →* G :=
  c.left.comp (torusHom.codRestrict _
    (fun p => borel_le_parabolic₁ (mem_sup_right ⟨p,rfl⟩)))

theorem torusMap_injective : Function.Injective c.torusMap := by
  intro p q he
  exact torusHom_injective (congrArg Subtype.val (c.left_injective he))

private theorem torusMap_right (p : Fˣ × Fˣ) :
    c.torusMap p = c.right (nativeTorus₂ p) := by
  let b : ChapterF.GreenBook.LieModels.G2.overlap (F := F) :=
    ⟨torusHom p,(nativeTorus₁ p).property,(nativeTorus₂ p).property⟩
  exact DFunLike.congr_fun c.compatible b

/-- The split torus marked by both endpoint maps, inside their whole overlap. -/
def markedTorus : Subgroup G := c.torusMap.range

theorem markedTorus_le_middle : c.markedTorus ≤ c.middle.range := by
  rintro x ⟨p,rfl⟩
  exact ⟨⟨torusHom p,(nativeTorus₁ p).property,(nativeTorus₂ p).property⟩,rfl⟩

theorem weylS_torusMap (l m : Fˣ) :
    MulAut.conj (c.left nativeS) (c.torusMap (l,m)) = c.torusMap (m,l) := by
  change c.left nativeS * c.left (nativeTorus₁ (l,m)) * (c.left nativeS)⁻¹ = _
  rw [←map_inv,←map_mul,←map_mul]
  apply congrArg c.left
  exact Subtype.ext (weylS_torus l m)

theorem weylR_torusMap (l m : Fˣ) :
    MulAut.conj (c.right nativeR) (c.torusMap (l,m)) = c.torusMap (l,l*m⁻¹) := by
  rw [c.torusMap_right,c.torusMap_right]
  change c.right nativeR * c.right (nativeTorus₂ (l,m)) * (c.right nativeR)⁻¹ = _
  rw [←map_inv,←map_mul,←map_mul]
  apply congrArg c.right
  exact Subtype.ext (weylR_torus l m)

def weylProduct : G := c.left nativeS*c.right nativeR

theorem weylProduct_torusMap (l m : Fˣ) :
    MulAut.conj c.weylProduct (c.torusMap (l,m)) = c.torusMap (l*m⁻¹,l) := by
  change (MulAut.conj (c.left nativeS*c.right nativeR)) _ = _
  rw [map_mul,MulAut.mul_apply,c.weylR_torusMap,c.weylS_torusMap]

/-- The canonical half-turn inverts every element of the same marked torus. -/
theorem weylProduct_cube_torusMap (l m : Fˣ) :
    MulAut.conj (c.weylProduct^3) (c.torusMap (l,m)) = c.torusMap (l⁻¹,m⁻¹) := by
  rw [map_pow]
  change MulAut.conj c.weylProduct (MulAut.conj c.weylProduct
    (MulAut.conj c.weylProduct (c.torusMap (l,m)))) = _
  rw [c.weylProduct_torusMap,c.weylProduct_torusMap,c.weylProduct_torusMap]
  congr 1
  apply Prod.ext <;> dsimp <;> simp [mul_assoc,mul_comm,mul_left_comm]

theorem weylProduct_cube_inverts {x : G} (hx : x∈c.markedTorus) :
    MulAut.conj (c.weylProduct^3) x = x⁻¹ := by
  obtain ⟨⟨l,m⟩,rfl⟩ := hx
  rw [c.weylProduct_cube_torusMap,←map_inv]
  rfl

/-- The sixth-power obstruction lies in the full ambient torus centralizer. -/
theorem weylProduct_six_mem_centralizer :
    c.weylProduct^6 ∈ centralizer (c.markedTorus : Set G) := by
  intro x hx
  apply (mul_inv_eq_iff_eq_mul.mp ?_).symm
  change MulAut.conj (c.weylProduct^6) x=x
  rw [show 6=3*2 from rfl,pow_mul,map_pow]
  change MulAut.conj (c.weylProduct^3) (MulAut.conj (c.weylProduct^3) x)=x
  rw [c.weylProduct_cube_inverts hx,map_inv,c.weylProduct_cube_inverts hx,inv_inv]

/-- There is no involution in the marked torus in characteristic two. -/
theorem markedTorus_sq_eq_one [CharP F 2] {x : G}
    (hx : x∈c.markedTorus) (hsq : x^2=1) : x=1 := by
  obtain ⟨⟨l,m⟩,rfl⟩ := hx
  have hp : (l,m)^2=(1 : Fˣ × Fˣ) := c.torusMap_injective (by
    simpa only [map_pow,map_one] using hsq)
  have hu (a : Fˣ) (ha : a^2=1) : a=1 := by
    apply Units.ext
    change (a:F)=1
    have hh : (a:F)^2=1 := congrArg Units.val ha
    rcases sq_eq_one_iff.mp hh with h|h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  have hl : l=1 := hu l (congrArg Prod.fst hp)
  have hm : m=1 := hu m (congrArg Prod.snd hp)
  rw [hl,hm]
  exact map_one c.torusMap

/-- Membership in the torus kills the sixth-power obstruction: the cube
both commutes with this power and inverts it. -/
theorem weylProduct_six_eq_one_of_mem [CharP F 2]
    (hm : c.weylProduct^6∈c.markedTorus) : c.weylProduct^6=1 := by
  have hi := c.weylProduct_cube_inverts hm
  have hc : MulAut.conj (c.weylProduct^3) (c.weylProduct^6)=c.weylProduct^6 :=
    mul_inv_eq_iff_eq_mul.mpr (Commute.pow_pow (Commute.refl c.weylProduct) 3 6).eq
  have hs : (c.weylProduct^6)^2=1 := by
    have he := hc.symm.trans hi
    rw [pow_two]
    nth_rw 1 [he]
    exact inv_mul_cancel _
  exact c.markedTorus_sq_eq_one hm hs

/-- Self-centralization of the actual marked torus suffices for the
canonical Weyl relation, without assuming a polygon or a model isomorphism. -/
theorem weylProduct_six_eq_one_of_torus_centralizer [CharP F 2]
    (hC : centralizer (c.markedTorus : Set G) ≤ c.markedTorus) :
    c.weylProduct^6=1 :=
  c.weylProduct_six_eq_one_of_mem (hC c.weylProduct_six_mem_centralizer)

theorem weylProduct_pow_torusMap (k : ℕ) (p : Fˣ × Fˣ) :
    MulAut.conj (c.weylProduct^k) (c.torusMap p) = c.torusMap ((torusRotation^k) p) := by
  induction k with
  | zero => simp only [pow_zero,map_one,MulAut.one_apply]
  | succ k ih =>
    rw [pow_succ' c.weylProduct,map_mul,MulAut.mul_apply,ih,pow_succ' torusRotation]
    exact c.weylProduct_torusMap _ _

/-- The canonical Weyl product has order divisible by six, including over F₄. -/
theorem six_dvd_orderOf_weylProduct [Finite F] [CharP F 2] (hq : 2<Nat.card F) :
    6 ∣ orderOf c.weylProduct := by
  rw [←torusRotation_order (F := F) hq]
  apply orderOf_dvd_of_pow_eq_one
  apply MulEquiv.ext
  intro p
  apply c.torusMap_injective
  have hh := c.weylProduct_pow_torusMap (orderOf c.weylProduct) p
  simpa only [pow_orderOf_eq_one,map_one,MulAut.one_apply] using hh.symm

/-- In a finite source completion the canonical product cannot have order below six. -/
theorem six_le_orderOf_weylProduct [Finite F] [CharP F 2] [Finite G]
    (hq : 2<Nat.card F) : 6 ≤ orderOf c.weylProduct :=
  Nat.le_of_dvd (orderOf_pos c.weylProduct) (c.six_dvd_orderOf_weylProduct hq)

theorem weylProduct_order_of_torus_centralizer [Finite F] [CharP F 2]
    (hq : 2<Nat.card F) (hC : centralizer (c.markedTorus : Set G) ≤ c.markedTorus) :
    orderOf c.weylProduct=6 :=
  Nat.dvd_antisymm
    (orderOf_dvd_of_pow_eq_one (c.weylProduct_six_eq_one_of_torus_centralizer hC))
    (c.six_dvd_orderOf_weylProduct hq)

/-- The torus-centralizer condition feeds the existing concrete recognition,
with both parabolic embeddings unchanged. -/
theorem nonempty_mulEquiv_of_torus_centralizer [Finite F] [CharP F 2]
    (hc : c.left.range ⊓ c.right.range=c.middle.range)
    (hC : centralizer (c.markedTorus : Set G) ≤ c.markedTorus) :
    Nonempty (G ≃* Model F) :=
  c.nonempty_mulEquiv_of_weyl hc (c.weylProduct_six_eq_one_of_torus_centralizer hC)

end Completion
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2CompletionGeometry

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open G2CompletionGeometry
variable {G : Type*} [Group G] {L H : Subgroup G} {F : Type} [Field F]

/-- The native split torus transported through the literal whole-overlap map. -/
def g2MarkedTorus
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse) : Subgroup G :=
  (splitTorus.subgroupOf (ChapterF.GreenBook.LieModels.G2.overlap (F := F))).map
    ((ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
      ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1).subtype.comp
      e.middle.symm.toMonoidHom)

theorem mem_g2MarkedTorus
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)
    (b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
      ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G)) :
    b.val∈g2MarkedTorus e ↔ (e.middle b).val∈splitTorus := by
  constructor
  · rintro ⟨a,ha,he⟩
    have he' : e.middle.symm a=b := Subtype.ext he
    rwa [←he',e.middle.apply_symm_apply]
  · intro hb
    exact ⟨e.middle b,hb,congrArg Subtype.val (e.middle.symm_apply_apply b)⟩

private theorem completion_markedTorus
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)
    (c : G2CompletionGeometry.Completion F G)
    (hl : c.left=(ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1).subtype.comp
      e.right.symm.toMonoidHom) : c.markedTorus=g2MarkedTorus e := by
  have ht (p : Fˣ × Fˣ) : c.torusMap p=
      (e.middle.symm ⟨torusHom p,(nativeTorus₁ p).property,(nativeTorus₂ p).property⟩).val := by
    change c.left (nativeTorus₁ p)=_
    rw [hl]
    exact congrArg Subtype.val (e.symm.right_commutes
      ⟨torusHom p,(nativeTorus₁ p).property,(nativeTorus₂ p).property⟩)
  apply le_antisymm
  · rintro x ⟨p,rfl⟩
    rw [ht]
    exact ⟨⟨torusHom p,(nativeTorus₁ p).property,(nativeTorus₂ p).property⟩,⟨p,rfl⟩,rfl⟩
  · rintro x ⟨b,hb,rfl⟩
    obtain ⟨p,hp⟩ := hb
    refine ⟨p,?_⟩
    rw [ht]
    exact congrArg (fun b => (e.middle.symm b).val) (Subtype.ext hp)

variable [Finite G] {T : Sylow 2 G} {W A B : Subgroup G} {n : ℕ}

/-- The actual source Weyl product has the sixfold torus action. The remaining
recognition obstruction is placed in the centralizer of this exact marked torus. -/
theorem Preparation.g2_weyl_torus_geometry
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse) :
    let w := (e.right.symm (nativeS (F := F))).val *
      (e.left.symm (nativeR (F := F))).val
    g2MarkedTorus e ≤ ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) ∧
      6 ∣ orderOf w ∧ 6 ≤ orderOf w ∧
      (∀ x∈g2MarkedTorus e, MulAut.conj (w^3) x=x⁻¹) ∧
      w^6∈centralizer (g2MarkedTorus e : Set G) := by
  obtain ⟨c,hl,hr,hm,_,_,_,_⟩ := d.g2_ambient_completion_geometry h hH hp F e
  have hD := completion_markedTorus e c hl
  have hw : c.weylProduct=(e.right.symm (nativeS (F := F))).val *
      (e.left.symm (nativeR (F := F))).val := by
    simp only [G2CompletionGeometry.Completion.weylProduct,hl,hr,MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom,coe_subtype]
  have hq : 2<Nat.card F := by
    rw [(d.g2_local_structure h hH.1.1.2 hp F (Or.inr ⟨e⟩)).1]
    exact Nat.pow_lt_pow_right (by decide : 1<(2:ℕ)) h.exponent
  dsimp only
  rw [←hD,←hw]
  exact ⟨hm ▸ c.markedTorus_le_middle,c.six_dvd_orderOf_weylProduct hq,
    c.six_le_orderOf_weylProduct hq,fun _ hx=>c.weylProduct_cube_inverts hx,
    c.weylProduct_six_mem_centralizer⟩

/-- A bound on the full ambient centralizer of the same marked torus discharges
the canonical Weyl relation and the concrete G₂ recognition step. -/
theorem Preparation.g2_ambient_recognition_of_torus_centralizer
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)
    (hC : centralizer (g2MarkedTorus e : Set G) ≤ g2MarkedTorus e) :
    Nat.card F=2^n ∧ Nonempty (G ≃* Model F) := by
  obtain ⟨c,hl,hr,_,ho,_,_,_⟩ := d.g2_ambient_completion_geometry h hH hp F e
  have hD := completion_markedTorus e c hl
  exact ⟨(d.g2_local_structure h hH.1.1.2 hp F (Or.inr ⟨e⟩)).1,
    c.nonempty_mulEquiv_of_torus_centralizer ho (by rwa [hD])⟩
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
