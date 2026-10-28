module

public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction.CoreReduction.Transport

/-!
# The faithful conjugate-core image

Source: Aschbacher–Smith, printed pp.569–570. Normal cyclic four-groups
are inverted first in the actual A₆ automorphism image, and then in the ambient
group by faithfulness. A conjugate reflection lies in the transposition
centralizer; this constructs the embedding of the core in `C₂ × D₈`.
-/

namespace CFSG.Quasithin.Chapter2.A6ShadowConstruction.CoreReduction

open Subgroup

variable {G : Type*} [Group G] [Finite G] (d : Setup G)

omit [Finite G] in
private theorem skAction_apply (k : d.sk) :
    skAction d k = action d ⟨k, k.property.1⟩ := by
  change action d (inclusion (show d.sk ≤ d.S from inf_le_left) k) = _
  congr 1

/-- The image of a subgroup of `S` under the supplied action. -/
@[expose] public def image (L : Subgroup G) : Subgroup AutA6 :=
  (L.subgroupOf d.S).map (action d)

public theorem image_le (L : Subgroup G) : image d L ≤ (imageSylow d : Subgroup AutA6) := by
  rw [imageSylow_eq_range]
  exact map_le_range _ _

public theorem image_normal (L : Subgroup G) (hn : (L.subgroupOf d.S).Normal) :
    ((image d L).subgroupOf (imageSylow d : Subgroup AutA6)).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer (image_le d L)).mpr
  rw [imageSylow_eq_range, MonoidHom.range_eq_map]
  have hN : (⊤ : Subgroup d.S) ≤ normalizer (L.subgroupOf d.S : Set d.S) := by
    rw [normalizer_eq_top_iff.mpr hn]
  exact (map_mono hN).trans (le_normalizer_map _)

private noncomputable def equiv_image_of_disjoint
    {Q R : Type*} [Group Q] [Group R] (f : Q →* R) (C : Subgroup Q)
    (h : Disjoint C f.ker) : C ≃* C.map f := by
  let j := f.comp C.subtype
  have hj : Function.Injective j := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro c hc
    exact Subtype.ext (disjoint_def.mp h c.property hc)
  have hr : j.range = C.map f := by
    ext r
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c, c.property, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, rfl⟩
  exact (MonoidHom.ofInjective hj).trans (MulEquiv.subgroupCongr hr)

/-- The conjugate of any subgroup of the core maps faithfully to its image. -/
public noncomputable def conjugateImageEquiv (L : Subgroup G) (hL : L ≤ d.core) :
    conjugate d.x L ≃* image d (conjugate d.x L) :=
  (subgroupOfEquivOfLe (conjugate_le d (hL.trans inf_le_left))).symm.trans
    (equiv_image_of_disjoint (action d) ((conjugate d.x L).subgroupOf d.S)
      (conjugate_disjoint_kernel d hL))

omit [Finite G] in
private theorem conjugate_twice_eq (V : Subgroup G) (hVS : V ≤ d.S)
    (hn : (V.subgroupOf d.S).Normal) : conjugate d.x (conjugate d.x V) = V := by
  have hxN : d.x ^ 2 ∈ normalizer (V : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hVS).mp hn d.square_mem
  unfold conjugate
  rw [map_map]
  have hm : (MulAut.conj d.x⁻¹).toMonoidHom.comp (MulAut.conj d.x⁻¹).toMonoidHom =
      (MulAut.conj (d.x ^ 2)⁻¹).toMonoidHom := by
    ext v
    simp [pow_two, mul_assoc]
  rw [hm]
  exact mem_normalizer_iff_map_conj_eq.mp ((normalizer (V : Set G)).inv_mem hxN)

/-- Inversion on the normal cyclic four-group, lifted from the finite image
of its conjugate. The square of `x` normalizes `V`, which identifies `Vˣˣ`
with `V` in the final conjugation step. -/
public theorem inverts_normal_cyclicFour (m : ModelGeometry (imageSylow d))
    (V : Subgroup G) (hVC : V ≤ d.core) (hn : (V.subgroupOf d.S).Normal)
    (hfour : Nonempty (V ≃* Multiplicative (ZMod 4)))
    {e : G} (he : e ∈ d.sk) (he2 : e ^ 2 = 1) (hne : e ∉ zpowers d.zK) :
    ∀ v ∈ V, (d.x⁻¹ * e * d.x)⁻¹ * v * (d.x⁻¹ * e * d.x) = v⁻¹ := by
  let VX := conjugate d.x V
  have hVXS : VX ≤ d.S := conjugate_le d (hVC.trans inf_le_left)
  have hnX : (VX.subgroupOf d.S).Normal := conjugate_normal d (hVC.trans inf_le_left) hn
  have hfX : Nonempty (image d VX ≃* Multiplicative (ZMod 4)) := by
    obtain ⟨f⟩ := hfour
    exact ⟨(conjugateImageEquiv d V hVC).symm.trans
      (((MulAut.conj d.x⁻¹).subgroupMap V).symm.trans f)⟩
  have heZ := skAction_noncentral d he hne
  have heD : skAction d ⟨e, he⟩ ∈ innerSylow (imageSylow d) := by
    rw [← skAction_range]
    exact ⟨⟨e, he⟩, rfl⟩
  have hei2 : skAction d ⟨e, he⟩ ^ 2 = 1 := by
    have h : (⟨e, he⟩ : d.sk) ^ 2 = 1 := Subtype.ext he2
    rw [← map_pow, h, map_one]
  have hinv := m.inverts_normal_cyclicFour (image d VX) (image_le d VX)
    (image_normal d VX hnX) hfX heD hei2 heZ
  have heN : (⟨e, he.1⟩ : d.S) ∈ normalizer (VX.subgroupOf d.S : Set d.S) := by
    rw [normalizer_eq_top_iff.mpr hnX]
    exact mem_top _
  have hLift := inversion_of_faithful_image (action d) (VX.subgroupOf d.S)
    (conjugate_disjoint_kernel d hVC) heN (fun v hv => by
      simpa only [map_mul, map_inv, skAction_apply] using
        hinv (action d v) (mem_map_of_mem (action d) hv))
  have hGX : ∀ v ∈ VX, e⁻¹ * v * e = v⁻¹ := by
    intro v hv
    exact congrArg Subtype.val (hLift (⟨v, hVXS hv⟩ : d.S) hv)
  intro v hv
  have hvXX : v ∈ conjugate d.x VX := (conjugate_twice_eq d V (hVC.trans inf_le_left) hn).symm ▸ hv
  obtain ⟨w, hw, rfl⟩ := hvXX
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  calc
    (d.x⁻¹ * e * d.x)⁻¹ * (d.x⁻¹ * w * d.x) * (d.x⁻¹ * e * d.x) =
        d.x⁻¹ * (e⁻¹ * w * e) * d.x := by group
    _ = (d.x⁻¹ * w * d.x)⁻¹ := by rw [hGX w hw]; group

private theorem exists_noncentral_involution (m : ModelGeometry (imageSylow d)) :
    ∃ e ∈ d.sk, e ^ 2 = 1 ∧ e ∉ zpowers d.zK := by
  obtain ⟨f⟩ := m.dihedral
  let j := (skEquiv d).trans f
  let e := j.symm (DihedralGroup.sr 0)
  refine ⟨e, e.property, ?_, ?_⟩
  · have he2 : e ^ 2 = 1 := by
      apply j.injective
      simp only [map_pow, map_one, e, j.apply_symm_apply]
      decide
    exact congrArg Subtype.val he2
  · intro heZ
    have hecenter : e ∈ center d.sk := by
      have hh : (e : G) ∈ (center d.sk).map d.sk.subtype := by
        change (e : G) ∈ (center (d.S ⊓ d.K : Subgroup G)).map (d.S ⊓ d.K).subtype
        rw [d.center_sk]
        exact heZ
      obtain ⟨k, hk, hke⟩ := hh
      exact (show k = e from Subtype.ext hke) ▸ hk
    have hc := congrArg j (mem_center_iff.mp hecenter (j.symm (DihedralGroup.r 1)))
    have hbad : DihedralGroup.r (1 : ZMod 4) * DihedralGroup.sr 0 =
        DihedralGroup.sr 0 * DihedralGroup.r 1 := by
      simpa only [map_mul, e, j.apply_symm_apply] using hc
    exact (by decide : DihedralGroup.r (1 : ZMod 4) * DihedralGroup.sr 0 ≠
      DihedralGroup.sr 0 * DihedralGroup.r 1) hbad

/-- The image of the conjugate reflection centralizes the inner Sylow factor. -/
public theorem conjugate_involution_centralizes_inner {e : G} (he : e ∈ d.sk) :
    action d ⟨d.x⁻¹ * e * d.x,
      conjugate_le d (L := d.sk) inf_le_left (conjugate_mem d he)⟩ ∈
      centralizer (innerSylow (imageSylow d) : Set AutA6) := by
  intro k hk
  rw [← skAction_range] at hk
  obtain ⟨k, rfl⟩ := hk
  have hc := d.sk_centralizes_conjugate k.property _ (conjugate_mem d he)
  have hcS : (⟨d.x⁻¹ * e * d.x,
      conjugate_le d (L := d.sk) inf_le_left (conjugate_mem d he)⟩ : d.S) * ⟨k, k.property.1⟩ =
      ⟨k, k.property.1⟩ * ⟨d.x⁻¹ * e * d.x,
        conjugate_le d (L := d.sk) inf_le_left (conjugate_mem d he)⟩ := Subtype.ext hc
  simpa only [map_mul, skAction_apply] using (congrArg (action d) hcS).symm

/-- Construct the actual injective homomorphism `S_C → C₂ × D₈`.
The containing image subgroup is the transposition centralizer, identified
with the internal product supplied by the finite-model calculation. -/
public theorem exists_core_embedding (m : ModelGeometry (imageSylow d)) :
    ∃ j : d.core →* Multiplicative (ZMod 2) × DihedralGroup 4, Function.Injective j := by
  obtain ⟨e, he, he2, hne⟩ := exists_noncentral_involution d m
  let a : d.S := ⟨d.x⁻¹ * e * d.x,
    conjugate_le d (L := d.sk) inf_le_left (conjugate_mem d he)⟩
  have haP : action d a ∈ (imageSylow d : Subgroup AutA6) := by
    rw [imageSylow_eq_range]
    exact ⟨a, rfl⟩
  have ha2 : action d a ^ 2 = 1 := by
    rw [← map_pow]
    have ha : a ^ 2 = 1 := by
      apply Subtype.ext
      change (d.x⁻¹ * e * d.x) ^ 2 = 1
      simpa only [map_pow, map_one, MulAut.conj_apply, inv_inv] using
        congrArg (MulAut.conj d.x⁻¹) he2
    rw [ha, map_one]
  have hcB := (m.involution_centralizer (action d a) haP ha2
    (conjugate_involution_centralizes_inner d he)
    (conjugate_involution_noninner d he he2 hne)).trans m.transposition_centralizer
  have himage : image d (conjugate d.x d.core) ≤
      zpowers m.transposition ⊔ innerSylow (imageSylow d) := by
    rw [← hcB]
    apply le_inf (image_le d _)
    rintro q ⟨c, hc, rfl⟩ b hb
    obtain rfl : b = action d a := Set.mem_singleton_iff.mp hb
    obtain ⟨v, hv, hvx⟩ := hc
    have hvx' : d.x⁻¹ * v * d.x = (c : G) := by simpa using hvx
    have hcomm : (a : G) * (c : G) = (c : G) * (a : G) := by
      have hh := congrArg (MulAut.conj d.x⁻¹) (hv.2 e he.2)
      have hh' : (d.x⁻¹ * e * d.x) * (d.x⁻¹ * v * d.x) =
          (d.x⁻¹ * v * d.x) * (d.x⁻¹ * e * d.x) := by
        simpa only [map_mul, MulAut.conj_apply, inv_inv] using hh
      simpa only [hvx'] using hh'
    simpa only [map_mul] using
      congrArg (action d) (show a * c = c * a from Subtype.ext hcomm)
  obtain ⟨model⟩ := m.product
  obtain ⟨j, hj⟩ := exists_embedding_of_image_le (action d)
    ((conjugate d.x d.core).subgroupOf d.S)
    (zpowers m.transposition ⊔ innerSylow (imageSylow d))
    (conjugate_disjoint_kernel d le_rfl) himage model
  let c : d.core ≃* ((conjugate d.x d.core).subgroupOf d.S) :=
    ((MulAut.conj d.x⁻¹).subgroupMap d.core).trans
      (subgroupOfEquivOfLe (conjugate_le d inf_le_left)).symm
  exact ⟨j.comp c.toMonoidHom, hj.comp c.injective⟩

end CFSG.Quasithin.Chapter2.A6ShadowConstruction.CoreReduction
