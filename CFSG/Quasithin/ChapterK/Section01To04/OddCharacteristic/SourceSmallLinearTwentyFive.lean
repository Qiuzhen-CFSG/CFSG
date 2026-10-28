module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Source
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.TwentyFive.SourceGeometry
public import Theory.SpecificGroups.PSL2.SquareFieldInvolutionLayers
public import GorensteinWalter.Section4.PSL2ReflectedTorusCard
public import GorensteinWalter.DihedralOddRotationCentralizer
public import Theory.ElementaryAbelian.Basic
public import Theory.ElementaryAbelian.Injective
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.TwentyFive
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.TwentyFive.ThreeDisplacement

/-!
# The PSL₂(25) exclusion at the cubic threshold

The proved central-cover comparison identifies the actual component with PSL₂(25).
An elementary actor has outer image of order at most two: a field involution
has inner linear coordinate, so an elementary subgroup cannot contain both a
nontrivial diagonal coordinate and a nontrivial field coordinate. Disjoint
actors are therefore cyclic and four conjugates contradict the degree bound.

A small actor meeting the component has rank three, hence contains an inner
four-group. In the involution centralizer's reflected torus of order twelve,
an inner reflection and its conjugate have product of order three. Its proved
displacement of at least eight contradicts the actor's saturated codimension six.
No FF assumption or extra geometry premise remains.

Source: Aschbacher--Smith K.2, printed p.453 (PDF p.464), citing
Guralnick--Malle, Classification of 2F-modules I, Proposition 4.1.
-/

public section
namespace CFSG.Quasithin.ChapterK.OddCharacteristic

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open GorensteinWalter
open CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion

private theorem outer_card_le_two {F B : Type*} [Field F] [Finite F]
    [Group B] [Finite B] [IsElementaryAbelian 2 B]
    (hF : Nat.card F = 25) (f : B →* PGammaL2 F) :
    letI : Fact (IsOddPrimePower (Nat.card F)) :=
      ⟨⟨5, 2, by decide, by decide, by decide, by simpa using hF⟩⟩
    Nat.card ((pGammaL2OuterProduct F).comp f).range ≤ 2 := by
  let hodd : IsOddPrimePower (Nat.card F) :=
    ⟨5, 2, by decide, by decide, by decide, by simpa using hF⟩
  let : Fact (IsOddPrimePower (Nat.card F)) := ⟨hodd⟩
  let : Finite (F ≃+* F) := Finite.of_injective
    (fun a : F ≃+* F => (a : F → F)) DFunLike.coe_injective
  let q := (pGammaL2OuterProduct F).comp f
  have hsplit (b : B) : (q b).1 = 1 ∨ (q b).2 = 1 := by
    by_cases hb : (f b).right = 1
    · exact Or.inr hb
    · left
      have hb2 : f b ^ 2 = 1 := by
        rw [← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 B) b, map_one]
      have hb1 : f b ≠ 1 := fun he => hb (congrArg SemidirectProduct.right he)
      exact (QuotientGroup.eq_one_iff _).mpr
        (Theory.PSL2.semilinear_involution_left_mem_psl hodd (f b)
          (orderOf_eq_prime hb2 hb1) hb)
  have haxes : (∀ b, (q b).1 = 1) ∨ (∀ b, (q b).2 = 1) := by
    by_cases ha : ∀ b, (q b).1 = 1
    · exact Or.inl ha
    · right
      push Not at ha
      obtain ⟨a, ha⟩ := ha
      have ha2 := (hsplit a).resolve_left ha
      intro b
      by_contra hb
      have hb1 := (hsplit b).resolve_right hb
      rcases hsplit (a * b) with hab | hab
      · simp only [map_mul, Prod.fst_mul, hb1, mul_one] at hab
        exact ha hab
      · simp only [map_mul, Prod.snd_mul, ha2, one_mul] at hab
        exact hb hab
  rcases haxes with hleft | hright
  · have hinj : Function.Injective (fun x : q.range => x.val.2) := by
      rintro ⟨x, a, rfl⟩ ⟨y, b, rfl⟩ he
      apply Subtype.ext
      exact Prod.ext ((hleft a).trans (hleft b).symm) he
    have hb := Nat.card_le_card_of_injective _ hinj
    have hc := FiniteField.card_ringAut_of_card_prime_pow (by decide : Nat.Prime 5)
      (show Nat.card F = 5 ^ 2 by simpa using hF)
    exact hb.trans_eq hc
  · have hinj : Function.Injective (fun x : q.range => x.val.1) := by
      rintro ⟨x, a, rfl⟩ ⟨y, b, rfl⟩ he
      apply Subtype.ext
      exact Prod.ext he ((hright a).trans (hright b).symm)
    have hb := Nat.card_le_card_of_injective _ hinj
    exact hb.trans_eq (pgl2_psl2Range_index_eq_two F hodd)

open RankOneSize.OuterGeneration

private theorem source_actor_card_bound {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (h : SourceAction ρ)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 25)
    (A : Subgroup G) (hA : IsElementaryTwo A) :
    Nat.card A ≤ 2 * Nat.card (A.subgroupOf (generalizedFitting G)) := by
  let L := generalizedFitting G
  let : IsElementaryAbelian 2 A := hA.2
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  obtain ⟨F, _, _, hc, ⟨eL⟩⟩ := RankOneSize.source_component_isPSL
    ρ h (by decide) (by decide) (by decide) hm
  let hodd : IsOddPrimePower (Nat.card F) :=
    ⟨5, 2, by decide, by decide, by decide, by simpa using hc⟩
  let : Fact (IsOddPrimePower (Nat.card F)) := ⟨hodd⟩
  let f := semilinearAction L eL hodd (by omega)
  let q := (pGammaL2OuterProduct F).comp (f.comp A.subtype)
  have hker (a : A) : a ∈ q.ker ↔ (a : G) ∈ L := by
    change f a ∈ (pGammaL2OuterProduct F).ker ↔ (a : G) ∈ L
    rw [pGammaL2OuterProduct_ker]
    exact involution_mem_inner_iff ρ L h.faithful eL hodd (by omega)
      (elemPow_eq_one_of_isElementaryAbelian (a : G) a.property)
  let ek : q.ker ≃ A.subgroupOf L := {
    toFun a := ⟨⟨a.val.val, (hker a.val).mp a.property⟩, a.val.property⟩
    invFun a := ⟨⟨a.val.val, a.property⟩, (hker _).mpr a.val.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hr : Nat.card q.range ≤ 2 := outer_card_le_two hc (f.comp A.subtype)
  calc
    Nat.card A = Nat.card q.ker * Nat.card q.range := by
      rw [← Subgroup.index_ker, Subgroup.card_mul_index]
    _ ≤ Nat.card q.ker * 2 := Nat.mul_le_mul_left _ hr
    _ = 2 * Nat.card (A.subgroupOf L) := by rw [Nat.card_congr ek, Nat.mul_comm]

open Subgroup GorensteinWalter
open scoped IsMulCommutative

private theorem inner_product {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 25) (B : Subgroup (PSL2 F))
    [IsElementaryAbelian 2 B] (hB : 2 < Nat.card B)
    (t : PSL2 F) (ht : orderOf t = 2)
    (hBt : B ≤ centralizer ({t} : Set (PSL2 F))) :
    ∃ g a : PSL2 F, a ∈ B ∧ Commute g t ∧ orderOf (a * (g * a * g⁻¹)) = 3 := by
  have hodd : IsOddPrimePower (Nat.card F) :=
    ⟨5, 2, by decide, by decide, by decide, by simpa using hF⟩
  have htI : IsInvolution t :=
    ⟨by intro he; simp [he] at ht, by simpa only [ht] using pow_orderOf_eq_one t⟩
  obtain ⟨T, s, hT, htT, hs, hsT, hinv, hC, heven, hc⟩ :=
    psl2_reflected_torus_card hodd htI
  let : IsCyclic T := hT
  let : CommGroup T := IsCyclic.commGroup
  have hcT : Nat.card T = 12 := by
    rw [hF] at hc
    rcases hc with hc | hc
    · norm_num at hc; exact hc
    · norm_num at hc
      rw [hc] at heven
      norm_num at heven
  have hnot : ¬ B ≤ T := by
    intro hle
    let : IsCyclic B := Subgroup.isCyclic_of_le hle
    have hd := IsElementaryAbelian.exponent_dvd_p 2 B
    rw [IsCyclic.exponent_eq_card] at hd
    have := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  obtain ⟨a, haB, haT⟩ := SetLike.not_le_iff_exists.mp hnot
  have ha2 : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a haB
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ha2)
  have haC := hBt haB
  rw [hC] at haC
  obtain ⟨u, hu, hau | hau⟩ :=
    (mem_sup_zpowers_of_involution_inverts hsT (by simpa only [pow_two] using hs.2) hinv).mp haC
  · exact (haT (hau ▸ hu)).elim
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := T) 3 (by rw [hcT]; decide)
  have hg3 : orderOf (g : PSL2 F) = 3 := (Subgroup.orderOf_coe g).trans hg
  have hgt : Commute (g : PSL2 F) t :=
    congrArg Subtype.val (mul_comm g ⟨t, htT⟩)
  have hag : a * (g : PSL2 F) * a⁻¹ = (g : PSL2 F)⁻¹ := by
    rw [hau]
    calc
      (u * s) * (g : PSL2 F) * (u * s)⁻¹ =
          u * (s * (g : PSL2 F) * s⁻¹) * u⁻¹ := by group
      _ = u * (g : PSL2 F)⁻¹ * u⁻¹ := by rw [hinv g g.property]
      _ = (g : PSL2 F)⁻¹ := by
        have he := congrArg Subtype.val (mul_comm (⟨u, hu⟩ : T) g⁻¹)
        change u * (g : PSL2 F)⁻¹ = (g : PSL2 F)⁻¹ * u at he
        rw [he, mul_inv_cancel_right]
  refine ⟨g, a, haB, hgt, ?_⟩
  have he : a * ((g : PSL2 F) * a * (g : PSL2 F)⁻¹) = ((g : PSL2 F) ^ 2)⁻¹ := by
    calc
      _ = (a * (g : PSL2 F) * a⁻¹) * (g : PSL2 F)⁻¹ := by rw [hai]; group
      _ = _ := by rw [hag]; group
  rw [he, orderOf_inv, (show Odd (orderOf (g : PSL2 F)) by rw [hg3]; decide).coprime_two_right.orderOf_pow,
    hg3]

private theorem source_inner_product {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (h : SourceAction ρ)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 25)
    (A : Subgroup G) (hA : IsElementaryTwo A) (hr : rank A = 3)
    (t : G) (htA : t ∈ A) (htL : t ∈ generalizedFitting G) (ht : orderOf t = 2) :
    ∃ g a : G, g ∈ generalizedFitting G ∧ a ∈ A ∧ a ∈ generalizedFitting G ∧
      Commute g t ∧ orderOf (a * (g * a * g⁻¹)) = 3 := by
  let L := generalizedFitting G
  let : IsElementaryAbelian 2 A := hA.2
  let B := A.subgroupOf L
  let : IsElementaryAbelian 2 B :=
    IsElementaryAbelian.comap_of_injective L.subtype L.subtype_injective A
  have hB : 2 < Nat.card B := by
    have hb := source_actor_card_bound ρ h hm A hA
    rw [hA.card_eq_two_pow_rank, hr] at hb
    change 2 < Nat.card (A.subgroupOf L)
    change 2 ^ 3 ≤ 2 * Nat.card (A.subgroupOf L) at hb
    omega
  obtain ⟨F, _, _, hc, ⟨eL⟩⟩ := RankOneSize.source_component_isPSL
    ρ h (by decide) (by decide) (by decide) hm
  let C := B.map eL.toMonoidHom
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.map eL.toMonoidHom
  have hC : 2 < Nat.card C := by
    rw [show Nat.card C = Nat.card B from card_map_of_injective eL.injective]
    exact hB
  let tL : L := ⟨t, htL⟩
  have htmodel : orderOf (eL tL) = 2 := by
    rw [eL.orderOf_eq, ← Subgroup.orderOf_coe]
    exact ht
  have hcent : C ≤ centralizer ({eL tL} : Set (PSL2 F)) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul]
    have hbc : b * tL = tL * b := by
      apply Subtype.ext
      exact congrArg (fun x : A => (x : G)) (mul_comm (⟨(b : G), hb⟩ : A) ⟨t, htA⟩)
    exact congrArg eL hbc
  obtain ⟨g, a, ha, hgt, horder⟩ := inner_product hc C hC (eL tL) htmodel hcent
  obtain ⟨a, ha, rfl⟩ := ha
  let gL := eL.symm g
  refine ⟨gL, a, gL.property, ha, a.property, ?_, ?_⟩
  · have he : Commute gL tL := by
      apply eL.injective
      simpa only [map_mul, gL, MulEquiv.apply_symm_apply] using hgt.eq
    exact congrArg Subtype.val he.eq
  · change orderOf ((a * (gL * a * gL⁻¹) : L) : G) = 3
    rw [Subgroup.orderOf_coe, ← eL.orderOf_eq]
    simpa only [map_mul, map_inv, gL, MulEquiv.apply_symm_apply,
      MulEquiv.coe_toMonoidHom] using horder

private theorem source_geometry {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (h : SourceAction ρ)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 25) :
    RankOneSmall.TwentyFive.ActorGeometry G := by
  intro A hA
  let : IsElementaryAbelian 2 A := hA.2
  by_cases hmeet : A ⊓ generalizedFitting G = ⊥
  · left
    have hb := source_actor_card_bound ρ h hm A hA
    rw [subgroupOf_eq_bot.mpr (disjoint_iff.mpr hmeet), card_bot, mul_one] at hb
    have hr : rank A = 1 := by
      rw [hA.card_eq_two_pow_rank] at hb
      have hlo := hA.rank_pos
      have hhi := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
        (show 2 ^ rank A ≤ 2 ^ 1 from hb)
      omega
    obtain ⟨t, htA, ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
    have ht2 : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t htA
    have htL : t ∉ generalizedFitting G := by
      intro htL
      exact ht1 (show t ∈ (⊥ : Subgroup G) from hmeet ▸ ⟨htA, htL⟩)
    exact ⟨hr, t, htA, orderOf_eq_prime ht2 ht1,
      RankOneSmall.TwentyFive.source_outer_four_conjugates ρ h hm t htL ht2⟩
  · right
    obtain ⟨t, htA, ht1⟩ :=
      (A ⊓ generalizedFitting G).bot_or_exists_ne_one.resolve_left hmeet
    have ht : orderOf t = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian t htA.1) ht1
    exact ⟨t, htA.1, htA.2, ht, fun hr =>
      source_inner_product ρ h hm A hA hr t htA.1 htA.2 ht⟩

/-- Strict K.2 bound on the original action, retaining all ambient outer actors. -/
theorem source_pslTwo_twentyFive_cubic_bound {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (h : SourceAction ρ)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 25) :
    2 < cubicRatio ρ :=
  RankOneSmall.TwentyFive.source_exclusion_of_calculations ρ h hm
    (source_geometry ρ h hm) (RankOneSmall.TwentyFive.source_threeDisplacementBound ρ h hm)

/-- The PSL₂(25) marking is impossible under the threshold-two source hypotheses. -/
theorem not_pslTwo_twentyFive {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
    (hs : RankOne.SourceHypotheses ρ L)
    (hm : ClassicalGroup.IsPSL (L ⧸ center L) 2 25) : False := by
  rcases hs with ⟨hsq, hfit, hquasi, hfaith, hirr, hsmall⟩
  subst L
  exact (not_lt_of_ge hsmall)
    (source_pslTwo_twentyFive_cubic_bound ρ ⟨hsq, hquasi, hfaith, hirr⟩ hm)

end CFSG.Quasithin.ChapterK.OddCharacteristic
