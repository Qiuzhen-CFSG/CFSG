module

public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.Quotients
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.QuotientModule.Alternating
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Statements
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.ConjugateIntersections.Orbits.Generation


/-!
# Involution geometry and the K-orbit obstruction in J.2.7

The earlier source results prove that s and z are nonconjugate involutions,
that S and hence T_s lie in K, and that T_s is the literal set product
S₀S₁. J.2.6 puts every member of sᴳ ∩ H in K minus Q.

The printed K-orbit assertion in J.2.7(8) conflicts with these facts and
C_H(s) = T_s, the input supplied by the normalizer branch. Indeed K is a
proper subgroup of H, while C_H(s) lies in K. Conjugating s by an element
of H minus K therefore gives a second K-class in the same ambient s-class.
The L-conjugates of U generate S and cannot all lie in Q; elementary fusion
thus also gives a z-class involution in K minus Q. The final theorem retains
three actual elements of K in pairwise distinct K-conjugacy classes.

This is an obstruction to the requested source assertion, not a proof of
J.2.7(8). The printed proof establishes H-transitivity; replacing H by K
would contradict the witnesses below. The equality C_H(s) = T_s and the
preceding J.2.6 fusion are explicit inputs. No Aut(A₆) marking, triple-cover
identification, five-core calculation, or later Suzuki recognition is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.2(1),(5), J.2.3(1–3), J.2.6, and J.2.7(8),(10), printed pp.432–437
(PDF pp.443–448 of `refs/quasithin.pdf`).
-/

public section
noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterJ.Centralizers.InvolutionGeometry
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

private def singer : SpecialCore.SingerChoice d.toTypeRuSetup c.sylowThree :=
  ⟨c.B7, c.B7_le, c.B7_card, c.B_normalizes⟩

/-- The chosen generator of the source center has order two. -/
theorem z_order : orderOf c.z = 2 := by
  have h := d.card_Z
  rwa [c.z_generator, Nat.card_zpowers] at h

/-- The chosen nonidentity member of the Singer-fixed four-group is an involution. -/
theorem s_order : orderOf c.s = 2 := by
  let e : c.S0 ≃* Multiplicative (ZMod 2 × ZMod 2) :=
    (singer c).fixedCoreEquivFour d.toTypeRuSetup c.sylowThree
  have hs2 : (⟨c.s, c.s_mem⟩ : c.S0) ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, map_one, pow_two]
    change (e ⟨c.s, c.s_mem⟩).toAdd + (e ⟨c.s, c.s_mem⟩).toAdd = 0
    exact CharTwo.add_self_eq_zero _
  exact orderOf_eq_prime (congrArg Subtype.val hs2) c.s_ne_one

/-- The source involutions s and z are not conjugate, by J.2.3(2). -/
theorem s_not_isConj_z : ¬ IsConj c.s c.z := by
  intro h
  apply SpecialCore.not_isConj_of_mem_fixedCore d.toTypeRuSetup d.card_Z
    c.B7 c.B7_card c.z c.z_mem_Z _ c.s c.s_mem h.symm
  intro hz
  have hh := z_order c
  simp [hz] at hh

/-- The earlier parabolic residual absorbs S into the actual two-residual K. -/
theorem S_le_K (d : LocalSetup G) : d.toTypeRuSetup.S ≤ d.toTypeRuSetup.K :=
  d.S_le_L₁.trans (embedded_pResidual_mono 2 inf_le_right)

/-- The source two-centralizer lies in K, independently of ambient Sylow promotion. -/
theorem Ts_le_K : c.Ts ≤ d.toTypeRuSetup.K := inf_le_left.trans (S_le_K d)

/-- The chosen s belongs to the actual two-residual K. -/
theorem s_mem_K : c.s ∈ d.toTypeRuSetup.K := S_le_K d c.s_mem.1

/-- The source product is equality of literal subsets of G, retaining both factors. -/
theorem Ts_product : (c.Ts : Set G) = (c.S0 : Set G) * (c.S1 : Set G) := by
  obtain ⟨e, he⟩ := ((singer c).source_conclusions d c.sylowThree).three
    c.s c.s_mem c.s_ne_one |>.2.1
  change c.S0 × c.S1 ≃* c.Ts at e
  change ∀ (a : c.S0) (m : c.S1), (e (a, m) : G) = (a : G) * (m : G) at he
  ext x
  constructor
  · intro hx
    let y := e.symm ⟨x, hx⟩
    refine Set.mem_mul.mpr ⟨y.1, y.1.property, y.2, y.2.property, ?_⟩
    exact (he y.1 y.2).symm.trans (congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩))
  · rintro ⟨a, ha, b, hb, rfl⟩
    have hm := (e (⟨a, ha⟩, ⟨b, hb⟩)).property
    rw [he] at hm
    exact hm

theorem s_class_mem_K_diff_Q
    (h26 : Fusion.SourceJ26 d.toTypeRuSetup c.z)
    {x : G} (hxH : x ∈ d.toTypeRuSetup.H) (hx : IsConj c.s x) :
    x ∈ Fusion.involutionsOutside d.toTypeRuSetup.K d.toTypeRuSetup.Q := by
  have hxo : orderOf x = 2 := by
    obtain ⟨g, rfl⟩ := isConj_iff.mp hx
    exact ((MulAut.conj g).orderOf_eq c.s).trans (s_order c)
  have hxn : ¬ IsConj x c.z := fun hh => s_not_isConj_z c (hx.trans hh)
  refine ⟨?_, ?_, hxo⟩
  · by_contra hn
    exact hxn (h26.1.2.2 x ⟨hxH, hn, hxo⟩)
  · intro hxQ
    exact hxn (h26.2.2.1 x hxQ hxo)

private theorem exists_H_not_K : ∃ h : d.toTypeRuSetup.H, (h : G) ∉ d.toTypeRuSetup.K := by
  obtain ⟨h, hh⟩ := d.ru2.quotient_surjective (Equiv.swap (0 : Fin 5) 1)
  refine ⟨h, ?_⟩
  intro hk
  have hm : d.ru2.quotientMap h ∈ alternatingGroup (Fin 5) := by
    rw [← d.toTypeRuSetup.quotientMap_K]
    exact mem_map_of_mem d.ru2.quotientMap hk
  rw [hh] at hm
  change Equiv.Perm.sign (Equiv.swap (0 : Fin 5) 1) = 1 at hm
  norm_num [Equiv.Perm.sign_swap] at hm

theorem exists_s_class_not_K_conjugate
    (hHs : d.toTypeRuSetup.H ⊓ c.Gs = c.Ts) :
    ∃ t : G, t ∈ d.toTypeRuSetup.H ∧ IsConj c.s t ∧
      ¬ ∃ k : d.toTypeRuSetup.K, (k : G) * c.s * (k : G)⁻¹ = t := by
  obtain ⟨h, hh⟩ := exists_H_not_K (d := d)
  refine ⟨(h : G) * c.s * (h : G)⁻¹, ?_, isConj_iff.mpr ⟨h, rfl⟩, ?_⟩
  · exact d.toTypeRuSetup.H.mul_mem
      (d.toTypeRuSetup.H.mul_mem h.property (d.S_le_H c.s_mem.1))
      (d.toTypeRuSetup.H.inv_mem h.property)
  · rintro ⟨k, he⟩
    have haH : (k : G)⁻¹ * h ∈ d.toTypeRuSetup.H :=
      d.toTypeRuSetup.H.mul_mem
        (d.toTypeRuSetup.H.inv_mem (d.toTypeRuSetup.K_le_H k.property)) h.property
    have haC : (k : G)⁻¹ * h ∈ c.Gs := by
      apply mem_centralizer_singleton_iff.mpr
      apply mul_inv_eq_iff_eq_mul.mp
      calc
        ((k : G)⁻¹ * h) * c.s * ((k : G)⁻¹ * h)⁻¹ =
            (k : G)⁻¹ * ((h : G) * c.s * (h : G)⁻¹) * k := by group
        _ = (k : G)⁻¹ * ((k : G) * c.s * (k : G)⁻¹) * k := by rw [he]
        _ = c.s := by group
    have haK := Ts_le_K c (hHs ▸ (show (k : G)⁻¹ * h ∈ d.toTypeRuSetup.H ⊓ c.Gs from ⟨haH, haC⟩))
    apply hh
    simpa only [mul_inv_cancel_left] using d.toTypeRuSetup.K.mul_mem k.property haK

theorem not_K_transitive_s_class
    (hHs : d.toTypeRuSetup.H ⊓ c.Gs = c.Ts)
    (h26 : Fusion.SourceJ26 d.toTypeRuSetup c.z) :
    ¬ Fusion.TransitiveOn d.toTypeRuSetup.K
      {x : G | IsConj c.s x ∧ x ∈ Fusion.involutionsOutside
        d.toTypeRuSetup.K d.toTypeRuSetup.Q} := by
  obtain ⟨t, htH, ht, hnt⟩ := exists_s_class_not_K_conjugate c hHs
  intro htrans
  exact hnt (htrans ⟨IsConj.refl c.s,
    s_class_mem_K_diff_Q c h26 (d.S_le_H c.s_mem.1) (IsConj.refl c.s)⟩
    ⟨ht, s_class_mem_K_diff_Q c h26 htH ht⟩)


theorem exists_z_class_mem_K_diff_Q
    (h26 : Fusion.SourceJ26 d.toTypeRuSetup c.z) :
    ∃ w : G, IsConj c.z w ∧
      w ∈ Fusion.involutionsOutside d.toTypeRuSetup.K d.toTypeRuSetup.Q := by
  classical
  have hex : ∃ l : d.L, ∃ u ∈ d.toTypeRuSetup.U,
      (MulAut.conj (l : G)) u ∉ d.toTypeRuSetup.Q := by
    by_contra! hn
    have hSQ : d.toTypeRuSetup.S ≤ d.toTypeRuSetup.Q := by
      rw [← ConjugateIntersections.conjugateSpan_eq_S d]
      apply iSup_le
      intro l
      rintro _ ⟨u, hu, rfl⟩
      exact hn l u hu
    apply d.Q_ne_S
    apply Eq.symm
    apply Subgroup.eq_of_le_of_card_ge hSQ
    rw [d.ru1.card_S, d.ru2.card_Q d.card_Z]
  obtain ⟨l, u, hu, hwQ⟩ := hex
  let w := (MulAut.conj (l : G)) u
  have hu1 : u ≠ 1 := by
    intro he
    apply hwQ
    simpa only [he, map_one] using d.toTypeRuSetup.Q.one_mem
  have hzw : IsConj c.z w :=
    (h26.2.2.2.2.2 u hu hu1).symm.trans (isConj_iff.mpr ⟨l, rfl⟩)
  have hwS : w ∈ d.toTypeRuSetup.S :=
    ConjugateIntersections.conjugateU_le_S d l l.property
      (mem_map_of_mem (MulAut.conj (l : G)).toMonoidHom hu)
  refine ⟨w, hzw, S_le_K d hwS, hwQ, ?_⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp hzw
  rw [← hg]
  exact ((MulAut.conj g).orderOf_eq c.z).trans (z_order c)

/-- Three pairwise distinct K-conjugacy classes occur in K minus Q.
The first two belong to the ambient s-class; the third belongs to the z-class. -/
theorem exists_three_K_classes
    (hHs : d.toTypeRuSetup.H ⊓ c.Gs = c.Ts)
    (h26 : Fusion.SourceJ26 d.toTypeRuSetup c.z) :
    ∃ a b w : d.toTypeRuSetup.K,
      (a : G) ∈ Fusion.involutionsOutside d.toTypeRuSetup.K d.toTypeRuSetup.Q ∧
      (b : G) ∈ Fusion.involutionsOutside d.toTypeRuSetup.K d.toTypeRuSetup.Q ∧
      (w : G) ∈ Fusion.involutionsOutside d.toTypeRuSetup.K d.toTypeRuSetup.Q ∧
      IsConj c.s (a : G) ∧ IsConj c.s (b : G) ∧ IsConj c.z (w : G) ∧
      ¬ IsConj a b ∧ ¬ IsConj a w ∧ ¬ IsConj b w := by
  obtain ⟨t, htH, ht, hnt⟩ := exists_s_class_not_K_conjugate c hHs
  obtain ⟨w, hzw, hw⟩ := exists_z_class_mem_K_diff_Q c h26
  have hs := s_class_mem_K_diff_Q c h26 (d.S_le_H c.s_mem.1) (IsConj.refl c.s)
  have htm := s_class_mem_K_diff_Q c h26 htH ht
  refine ⟨⟨c.s, hs.1⟩, ⟨t, htm.1⟩, ⟨w, hw.1⟩,
    hs, htm, hw, IsConj.refl c.s, ht, hzw, ?_, ?_, ?_⟩
  · intro hab
    obtain ⟨k, hk⟩ := isConj_iff.mp hab
    exact hnt ⟨k, congrArg Subtype.val hk⟩
  · intro haw
    exact s_not_isConj_z c ((d.toTypeRuSetup.K.subtype.map_isConj haw).trans hzw.symm)
  · intro hbw
    exact s_not_isConj_z c (ht.trans
      ((d.toTypeRuSetup.K.subtype.map_isConj hbw).trans hzw.symm))

end CFSG.Quasithin.ChapterJ.Centralizers.InvolutionGeometry
