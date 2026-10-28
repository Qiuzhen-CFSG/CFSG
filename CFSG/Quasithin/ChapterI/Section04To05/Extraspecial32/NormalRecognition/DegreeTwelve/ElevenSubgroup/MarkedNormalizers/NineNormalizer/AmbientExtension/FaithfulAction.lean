module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.NineNormalizer.AmbientExtension.Reduction
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding
public import Theory.SpecificGroups.GL2.ThreeQuaternionUniqueness
public import Theory.GroupAction.PrimeGroupFixedImage
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The self-centralizing nine-group extension

Conjugation on the literal marked subgroup D embeds N_G(D)/D in GL₂(3).
The order bound 432 forces the whole matrix image. Since b = uz acts as
inversion, its image is central; coprime fixed-point lifting makes the
restriction to C_{N_G(D)}(b) surjective, and D ∩ C_G(b) = 1 makes it an
isomorphism. This supplies the compatible splitting, with the original z
in the complement.

The image of the literal quaternion intersection P ∩ L is the unique Q₈
in GL₂(3). Comparing image orders identifies it with the image of
K = L ∩ N_G(D), proving normality relative to N_G(D). In the same complement,
b maps to -I, while z maps to a noncentral involution. A kernel-checked
calculation on the 81 matrices supplies its involution partner v with
|vz| = 3; the complement isomorphism transports it to the original group.

The final theorem is conditional precisely on C_G(D) = D. Eliminating the
other centralizer case belongs to the ambient-extension assembly.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), Lemma 4.9 and the following paragraph, pp.41–42.
-/

open Subgroup
namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.NineNormalizer.FaithfulAction
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {h : Hypotheses z} {a : SourceGeometry h}
private abbrev GLThree := Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)

private theorem card_GL : Nat.card GLThree = 48 := by
  rw [Matrix.card_GL_field]
  decide

private theorem full_action (s : SymmetricSixData h a) (m : M10NormalizerGeometry s)
    (hC : centralizer (s.markedNine : Set G) = s.markedNine) :
    ∃ i : MulAut s.markedNine →* GLThree, Function.Injective i ∧
      Function.Surjective (i.comp s.markedNine.normalizerMonoidHom) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : IsElementaryAbelian 3 s.markedNine := s.elementary_markedNine
  obtain ⟨i, hi⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (p := 3) (n := 2) s.markedNine (by rw [s.card_markedNine]; decide)
  refine ⟨i, hi, ?_⟩
  let f := i.comp s.markedNine.normalizerMonoidHom
  have hk : f.ker = s.markedNine.subgroupOf (normalizer (s.markedNine : Set G)) := by
    rw [MonoidHom.ker_comp_of_injective _ _ hi, normalizerMonoidHom_ker, hC]
  have hc : Nat.card f.ker = 9 := by
    rw [hk, Nat.card_congr (subgroupOfEquivOfLe s.markedNine.le_normalizer).toEquiv,
      s.card_markedNine]
  apply f.surjective_of_card_ker_le_div
  rw [hc, card_GL]
  have hd := card_normalizer_divisible_by_432 s m
  have hp : 0 < Nat.card (normalizer (s.markedNine : Set G)) := Nat.card_pos
  have hlo := Nat.le_of_dvd hp hd
  omega

private theorem relative_normal_K (s : SymmetricSixData h a) (m : M10NormalizerGeometry s)
    (f : normalizer (s.markedNine : Set G) →* GLThree)
    (hk : f.ker = s.markedNine.subgroupOf (normalizer (s.markedNine : Set G))) :
    ((s.markedK m.L).subgroupOf (normalizer (s.markedNine : Set G))).Normal := by
  let N := normalizer (s.markedNine : Set G)
  let K := (s.markedK m.L).subgroupOf N
  let Q := (m.P ⊓ m.L).subgroupOf N
  have hQN : m.P ⊓ m.L ≤ N := inf_le_left.trans (complement_le_normalizer s m)
  have hQK : Q ≤ K := fun x hx => ⟨hx.2, x.property⟩
  have hkerK : f.ker ≤ K := by
    rw [hk]
    exact fun x hx => ⟨m.D_le hx, x.property⟩
  have hfQ : Function.Injective (f.comp Q.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    have hxD : (x.val : G) ∈ s.markedNine := by
      have hh : x.val ∈ f.ker := hx
      rwa [hk] at hh
    have he : (x.val : G) = 1 := disjoint_def.mp m.disjoint hxD x.property.1
    exact mem_bot.mpr (Subtype.ext (Subtype.ext he))
  obtain ⟨e⟩ := m.quaternion
  let eQ : Q ≃* QuaternionGroup 2 := (subgroupOfEquivOfLe hQN).trans e
  let j := f.comp Q.subtype
  let eqJ : j.range ≃* QuaternionGroup 2 := (MonoidHom.ofInjective hfQ).symm.trans eQ
  have hr : j.range = Q.map f := by rw [MonoidHom.range_comp, range_subtype]
  have hQimage : Nonempty (Q.map f ≃* QuaternionGroup 2) :=
    ⟨(MulEquiv.subgroupCongr hr).symm.trans eqJ⟩
  have hQcard : Nat.card (Q.map f) = 8 := by
    obtain ⟨ee⟩ := hQimage
    rw [Nat.card_congr ee.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hKcard : Nat.card K = 72 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show s.markedK m.L ≤ N from inf_le_right)).toEquiv,
      m.card_K]
  have hker : Nat.card f.ker = 9 := by
    rw [hk, Nat.card_congr (subgroupOfEquivOfLe s.markedNine.le_normalizer).toEquiv,
      s.card_markedNine]
  have hKimage : Nat.card (K.map f) = 8 := by
    have hh := card_subgroup_of_ker_le f K hkerK
    rw [hKcard, hker] at hh
    omega
  have heq : Q.map f = K.map f := eq_of_le_of_card_ge (map_mono hQK)
    (by rw [hQcard, hKimage])
  have hnormal : (K.map f).Normal := by
    rw [← heq]
    exact Matrix.GeneralLinearGroup.three_quaternion_subgroup_normal _ hQimage
  change K.Normal
  rw [← comap_map_eq_self hkerK]
  exact hnormal.comap f

private theorem action_inverts (s : SymmetricSixData h a) (m : M10NormalizerGeometry s)
    (d : s.markedNine) :
    s.markedNine.normalizerMonoidHom
      ⟨s.u * z, m.b_mem_K.2⟩ d = d⁻¹ := by
  apply Subtype.ext
  exact s.uz_inverts_markedNine d d.property

private theorem action_b_central (s : SymmetricSixData h a) (m : M10NormalizerGeometry s)
    (i : MulAut s.markedNine →* GLThree)
    (hs : Function.Surjective (i.comp s.markedNine.normalizerMonoidHom)) :
    (i.comp s.markedNine.normalizerMonoidHom) ⟨s.u * z, m.b_mem_K.2⟩ ∈ center GLThree := by
  apply mem_center_iff.mpr
  intro y
  obtain ⟨x, rfl⟩ := hs y
  rw [← map_mul, ← map_mul]
  apply congrArg i
  rw [map_mul, map_mul]
  apply MulEquiv.ext
  intro d
  change s.markedNine.normalizerMonoidHom x
      (s.markedNine.normalizerMonoidHom ⟨s.u * z, m.b_mem_K.2⟩ d) =
    s.markedNine.normalizerMonoidHom ⟨s.u * z, m.b_mem_K.2⟩
      (s.markedNine.normalizerMonoidHom x d)
  rw [action_inverts s m, action_inverts s m, map_inv]

private theorem complement_bijective (s : SymmetricSixData h a) (m : M10NormalizerGeometry s)
    (f : normalizer (s.markedNine : Set G) →* GLThree)
    (hk : f.ker = s.markedNine.subgroupOf (normalizer (s.markedNine : Set G)))
    (hs : Function.Surjective f)
    (hb : f ⟨s.u * z, m.b_mem_K.2⟩ ∈ center GLThree) :
    Function.Bijective (f.comp
      (centralizer ({⟨s.u * z, m.b_mem_K.2⟩} : Set (normalizer (s.markedNine : Set G)))).subtype) := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let N := normalizer (s.markedNine : Set G)
  let b : N := ⟨s.u * z, m.b_mem_K.2⟩
  let C := centralizer ({b} : Set N)
  have hcard : Nat.card f.ker = 9 := by
    rw [hk, Nat.card_congr (subgroupOfEquivOfLe s.markedNine.le_normalizer).toEquiv,
      s.card_markedNine]
  have hb_order : orderOf b = 2 := by rw [← orderOf_coe, s.uz_order]
  have hp : IsPGroup 2 (zpowers b) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hb_order]; rfl)
  have hcent : centralizer (zpowers b : Set N) = C := by
    change centralizer (zpowers b : Set N) = centralizer ({b} : Set N)
    rw [zpowers_eq_closure, centralizer_closure]
  have htop : centralizer ((zpowers b).map f : Set GLThree) = ⊤ := by
    apply top_unique
    intro x _
    have hx : (zpowers b).map f ≤ centralizer ({x} : Set GLThree) := by
      rw [map_le_iff_le_comap, zpowers_le]
      exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hb x).symm
    intro y hy
    exact mem_centralizer_singleton_iff.mp (hx hy)
  have hm : C.map f = ⊤ := by
    rw [← hcent, centralizer_map_of_prime_free_kernel f hs (by rw [hcard]; decide) _ hp, htop]
  constructor
  · apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    have hxD : (x.val : G) ∈ s.markedNine := by
      have hh : x.val ∈ f.ker := hx
      rwa [hk] at hh
    have hxC : (x.val : G) ∈ Centralizer (s.u * z) := by
      apply mem_centralizer_singleton_iff.mpr
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property)
    have he : (x.val : G) = 1 := mem_bot.mp
      (s.markedNine_inf_centralizer_uz ▸ (show (x.val : G) ∈
        s.markedNine ⊓ Centralizer (s.u * z) from ⟨hxD, hxC⟩))
    exact mem_bot.mpr (Subtype.ext (Subtype.ext he))
  · intro y
    obtain ⟨x, hx, hxy⟩ := show y ∈ C.map f by rw [hm]; trivial
    exact ⟨⟨x, hx⟩, hxy⟩

private abbrev Mat := Matrix (Fin 2) (Fin 2) (ZMod 3)

private theorem central_matrix (A : Mat) (hs : A ^ 2 = 1) (hn : A ≠ 1)
    (h₁ : A * !![1,1;0,1] = !![1,1;0,1] * A)
    (h₂ : A * !![0,1;1,0] = !![0,1;1,0] * A) : A = -1 := by
  revert A
  decide +kernel

private theorem reflection_matrix : ∀ A : Mat,
    A ^ 2 = 1 → A ≠ 1 → A ≠ -1 →
    ∃ B : Mat, B ^ 2 = 1 ∧ (B * A) ^ 3 = 1 ∧ B * A ≠ 1 := by
  decide +kernel

private theorem central_value (t : GLThree) (hs : t ^ 2 = 1) (hn : t ≠ 1)
    (hc : t ∈ center GLThree) : t.val = -1 := by
  apply central_matrix t.val (congrArg Units.val hs) (fun he => hn (Units.ext he))
  · let x : GLThree := Matrix.GeneralLinearGroup.mkOfDetNeZero !![1,1;0,1] (by decide)
    exact congrArg Units.val ((mem_center_iff.mp hc x).symm)
  · let x : GLThree := Matrix.GeneralLinearGroup.mkOfDetNeZero !![0,1;1,0] (by decide)
    exact congrArg Units.val ((mem_center_iff.mp hc x).symm)

private theorem reflection_partner (t : GLThree) (hs : t ^ 2 = 1) (hn : t ≠ 1)
    (hm : t.val ≠ -1) : ∃ v : GLThree, v * v = 1 ∧ orderOf (v * t) = 3 := by
  obtain ⟨B, hB, hc, hnB⟩ := reflection_matrix t.val (congrArg Units.val hs)
    (fun he => hn (Units.ext he)) hm
  have hBB : B * B = 1 := by simpa only [pow_two] using hB
  let v : GLThree := ⟨B, B, hBB, hBB⟩
  refine ⟨v, Units.ext hBB, ?_⟩
  exact orderOf_eq_prime_iff.mpr ⟨Units.ext hc, fun he => hnB (congrArg Units.val he)⟩

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.NineNormalizer.FaithfulAction

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.NineNormalizer
open FaithfulAction
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {h : Hypotheses z} {a : SourceGeometry h}

/-- The self-centralizing branch constructs relative normality of the literal
K and the marked involution in N_G(D) ∩ C_G(uz), without a splitting premise. -/
public theorem nonempty_ambientData_of_self_centralizing (s : SymmetricSixData h a)
    (_n : SymmetricNormalizerData s) (m : M10NormalizerGeometry s)
    (hC : centralizer (s.markedNine : Set G) = s.markedNine) :
    Nonempty (AmbientData s m) := by
  obtain ⟨i, hi, hs⟩ := full_action s m hC
  let N := normalizer (s.markedNine : Set G)
  let f : N →* GLThree := i.comp s.markedNine.normalizerMonoidHom
  have hk : f.ker = s.markedNine.subgroupOf N := by
    rw [MonoidHom.ker_comp_of_injective _ _ hi, normalizerMonoidHom_ker, hC]
  let b : N := ⟨s.u * z, m.b_mem_K.2⟩
  let C := centralizer ({b} : Set N)
  let e : C ≃* GLThree := MulEquiv.ofBijective (f.comp C.subtype)
    (complement_bijective s m f hk hs (action_b_central s m i hs))
  let bc : C := ⟨b, mem_centralizer_singleton_iff.mpr rfl⟩
  let zn : N := ⟨z, complement_le_normalizer s m m.z_mem_P⟩
  let zc : C := ⟨zn, mem_centralizer_singleton_iff.mpr
    (Subtype.ext (s.u_commutes_z.symm.mul_right (Commute.refl z)).eq)⟩
  have hb2 : bc ^ 2 = 1 := Subtype.ext (Subtype.ext s.uz_sq)
  have hb1 : bc ≠ 1 := fun he => s.uz_ne_one
    (congrArg (fun x : C => (x.val : G)) he)
  have hz2 : zc ^ 2 = 1 := Subtype.ext (Subtype.ext
    (h.involution ▸ pow_orderOf_eq_one z))
  have hz1 : zc ≠ 1 := by
    intro he
    have hh : z = 1 := congrArg (fun x : C => (x.val : G)) he
    have ho := h.involution
    rw [hh, orderOf_one] at ho
    contradiction
  have hbcentral : e bc ∈ center GLThree := action_b_central s m i hs
  have hbval : (e bc).val = -1 := central_value (e bc)
    (by rw [← map_pow, hb2, map_one])
    (fun he => hb1 (e.injective (he.trans e.map_one.symm))) hbcentral
  have hzval : (e zc).val ≠ -1 := by
    intro he
    have he' : zc = bc := e.injective (Units.ext (he.trans hbval.symm))
    have heG : z = s.u * z := congrArg (fun x : C => (x.val : G)) he'
    have hu : s.u = 1 := mul_right_cancel (heG.symm.trans (one_mul z).symm)
    have ho := s.u_order
    rw [hu, orderOf_one] at ho
    contradiction
  obtain ⟨w, hw2, hwz⟩ := reflection_partner (e zc)
    (by rw [← map_pow, hz2, map_one])
    (fun he => hz1 (e.injective (he.trans e.map_one.symm))) hzval
  let v : C := e.symm w
  have hv2 : v * v = 1 := by
    apply e.injective
    simpa only [map_mul, map_one, v, e.apply_symm_apply] using hw2
  have hvz : orderOf (v * zc) = 3 := by
    rw [← e.orderOf_eq, map_mul]
    simpa only [v, e.apply_symm_apply] using hwz
  refine ⟨{ normal_K := relative_normal_K s m f hk
            v := (v.val : G)
            v_mem := v.val.property
            v_sq := congrArg (fun x : C => (x.val : G)) hv2
            v_commutes_b := ?_
            vz_order := ?_ }⟩
  · exact (show Commute (v.val : G) (s.u * z) from
      congrArg Subtype.val (mem_centralizer_singleton_iff.mp v.property)).symm
  · change orderOf ((v * zc).val : G) = 3
    rw [orderOf_coe, orderOf_coe]
    exact hvz

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.NineNormalizer
