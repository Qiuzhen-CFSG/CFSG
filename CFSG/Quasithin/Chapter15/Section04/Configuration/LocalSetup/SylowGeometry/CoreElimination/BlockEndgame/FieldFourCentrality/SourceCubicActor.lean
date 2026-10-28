module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.FieldFourCentrality.Setup
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.FieldFourCentrality.SourceCubicActor.Commutation

/-!
# Cubic source actions on the exchanged blocks

For the literal product K = L Lʳ, commutation gives a surjective projection
K → L/O₂(L): the intersection of the factors is central in L and hence lies
in O₂(L). Because U normalizes X and H = KU, the source equality
⟨Xᴴ⟩ = K implies that X also normally generates K inside K. Consequently
some source factor Xᵢ has nontrivial image under the projection. Its
two-perfection and quotient order three force this image to contain an
element of order three. Factoring that source element as l*m shows that
its conjugation on every element of U(L) is exactly conjugation by l.

The imported commutation theorem proves that the actual exchanged blocks
commute from their relative subnormality and quasisimple two-core quotients.
Combining it with the projection argument proves both normalization and the
actual cubic actor without further hypotheses or a field-order restriction.
The field-four specialization supplies these two inputs to the final
fixed-seed centrality assembly in the proof of 15.4.20.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, C.1.7–9,
printed pp.123–124, and proof of 15.4.20, printed p.1164.
-/

public section

open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.FieldFourCentrality
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {d : Source.Geometry G} {i j : Bool}

private theorem cubic_image_of_nontrivial {A Q : Type*} [Group A] [Finite A] [Group Q]
    (hA : IsPPerfect 2 A) (hcard : Nat.card (A ⧸ pCore 2 A) = 3)
    (f : A →* Q) (hf : f ≠ 1) : ∃ a : A, orderOf (f a) = 3 := by
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have h3 : 3 ∣ Nat.card f.range := by
    by_contra h3
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (pCore_isPGroup (p := 2) (G := A))
    have hc : Nat.card A = 2 ^ n * 3 := by
      rw [← (pCore 2 A).card_mul_index, index_eq_card, hcard, hn]
    have hd := Subgroup.card_range_dvd f
    rw [hc] at hd
    have hcop : (Nat.card f.range).Coprime 3 :=
      ((show Nat.Prime 3 from by decide).coprime_iff_not_dvd.mpr h3).symm
    have hp : IsPGroup 2 f.range := IsPGroup.of_card_dvd_pow (hcop.dvd_mul_right.mp hd)
    have he := hA.hom_eq_one_of_isPGroup hp f.rangeRestrict
    apply hf
    ext a
    exact congrArg Subtype.val (DFunLike.congr_fun he a)
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := f.range) 3 h3
  obtain ⟨x, hx⟩ := a.property
  refine ⟨x, ?_⟩
  rw [hx]
  exact (Subgroup.orderOf_mk _ _).symm.trans ha

private theorem short_center_le_core {A : Type*} [Group A]
    (hA : ChapterC.IsShort A) : center A ≤ pCore 2 A := by
  rw [← hA.fitting]
  apply le_trans ?_ (fitting_le_generalizedFitting A)
  exact le_sSup ⟨inferInstance, inferInstance⟩

omit [Finite G] in
private theorem central_product_projection (L M K : Subgroup G)
    (hL : ChapterC.IsShort L) (hcomm : L ≤ centralizer (M : Set G))
    (hprod : (L : Set G) * (M : Set G) = (K : Set G))
    (hLK : L ≤ K) (hMK : M ≤ K) :
    ∃ f : K →* (L ⧸ pCore 2 L), Function.Surjective f ∧
      ∀ (l : L) (m : M), f ⟨(l : G) * (m : G), K.mul_mem (hLK l.property) (hMK m.property)⟩ =
        QuotientGroup.mk' (pCore 2 L) l := by
  let p : L × M →* K := (inclusion hLK).noncommCoprod (inclusion hMK)
    (fun l m => by
      apply Subtype.ext
      exact (mem_centralizer_iff.mp (hcomm l.property) m m.property).symm)
  have hp : Function.Surjective p := by
    intro k
    have hk : (k : G) ∈ (L : Set G) * (M : Set G) := hprod.symm ▸ k.property
    obtain ⟨l, hl, m, hm, he⟩ := hk
    exact ⟨(⟨l, hl⟩, ⟨m, hm⟩), Subtype.ext he⟩
  let q := (QuotientGroup.mk' (pCore 2 L)).comp (MonoidHom.fst L M)
  have hk : p.ker ≤ q.ker := by
    rintro ⟨l, m⟩ hh
    have he : (l : G) * (m : G) = 1 := congrArg Subtype.val hh
    have hlM : (l : G) ∈ M := by
      rw [mul_eq_one_iff_eq_inv.mp he]
      exact M.inv_mem m.property
    have hlZ : l ∈ center L := by
      apply mem_center_iff.mpr
      intro z
      apply Subtype.ext
      exact (mem_centralizer_iff.mp (hcomm z.property) l hlM).symm
    exact (QuotientGroup.eq_one_iff l).mpr (short_center_le_core hL hlZ)
  let f := p.liftOfSurjective hp ⟨q, hk⟩
  have he (l : L) (m : M) : f (p (l, m)) = QuotientGroup.mk' (pCore 2 L) l := by
    exact p.liftOfRightInverse_comp_apply _ _ _ _
  refine ⟨f, ?_, he⟩
  intro a
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) a
  exact ⟨p (l, 1), he l 1⟩

/-- The source conjugate closure contains its original generators. -/
lemma wholeX_le_K (c : ContraryData κ d i j) : d.wholeX ≤ c.K := by
  intro x hx
  rw [← c.conjugate_closure]
  exact ⟨⟨x, c.X_le_H hx⟩, le_normalClosure hx, rfl⟩

/-- Since U normalizes X, its normal generation in H also detects maps out of K. -/
lemma hom_eq_one_of_kills_wholeX (c : ContraryData κ d i j)
    {Q : Type*} [Group Q] (f : c.K →* Q)
    (hf : ∀ x : d.wholeX, f ⟨x, wholeX_le_K c x.property⟩ = 1) : f = 1 := by
  let N := f.ker.map c.K.subtype
  have hKN : c.K ≤ N := by
    rw [← c.conjugate_closure]
    apply map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le (K := N.comap c.H.subtype)).mpr
    intro x hx
    obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp hax
    have hg : (g : G) ∈ (c.K : Set G) * (c.U : Set G) :=
      c.product_set.symm ▸ g.property
    obtain ⟨k, hk, u, hu, he⟩ := hg
    have hau : u * (a : G) * u⁻¹ ∈ d.wholeX :=
      (mem_normalizer_iff.mp (c.upper_lt.le.trans c.T_le_M₁ hu) (a : G)).mp ha
    let y : c.K := ⟨u * (a : G) * u⁻¹, wholeX_le_K c hau⟩
    have hy : y ∈ f.ker := hf ⟨_, hau⟩
    refine ⟨(⟨k, hk⟩ : c.K) * y * (⟨k, hk⟩ : c.K)⁻¹,
      (inferInstance : f.ker.Normal).conj_mem y hy ⟨k, hk⟩, ?_⟩
    change k * (u * (a : G) * u⁻¹) * k⁻¹ = (g : G) * (a : G) * (g : G)⁻¹
    rw [← he]
    simp only [mul_inv_rev, mul_assoc]
  ext k
  obtain ⟨z, hz, he⟩ := hKN k.property
  have hzk : z = k := Subtype.ext he
  exact MonoidHom.mem_ker.mp (hzk ▸ hz)


/-- The literal product of commuting blocks normalizes its first factor. -/
theorem normalizes_first_of_commuting (c : ContraryData κ d i j) (b : ExchangedBlock c)
    (hcomm : ⁅b.first, b.first.map (MulAut.conj b.exchanger).toMonoidHom⁆ = ⊥) :
    d.wholeX ≤ normalizer (b.first : Set G) := by
  apply (wholeX_le_K c).trans
  rw [← b.product]
  exact sup_le b.first.le_normalizer
    ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)).trans
      (Subgroup.centralizer_le_normalizer _))

/-- Commutation and the source normal closure force a genuine cubic coordinate. -/
theorem hasCubicActor_of_commuting (c : ContraryData κ d i j) (b : ExchangedBlock c)
    (hcomm : ⁅b.first, b.first.map (MulAut.conj b.exchanger).toMonoidHom⁆ = ⊥) :
    HasCubicActor c b := by
  let M := b.first.map (MulAut.conj b.exchanger).toMonoidHom
  have hLM : b.first ≤ centralizer (M : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hLK : b.first ≤ c.K := b.product ▸ le_sup_left
  have hMK : M ≤ c.K := b.product ▸ le_sup_right
  obtain ⟨f, hf, hflm⟩ := central_product_projection b.first M c.K b.model.2.1
    hLM b.product_set hLK hMK
  let Q := b.first ⧸ pCore 2 b.first
  let : IsSimpleGroup (Q ⧸ center Q) := b.quotient_quasisimple.simple
  let : Nontrivial Q := (QuotientGroup.mk'_surjective (center Q)).nontrivial
  have hfn : f ≠ 1 := by
    intro he
    obtain ⟨q, hq⟩ := exists_ne (1 : Q)
    obtain ⟨k, rfl⟩ := hf q
    exact hq (DFunLike.congr_fun he k)
  have hX (a : Bool) : d.X a ≤ d.wholeX := by
    cases a
    · exact le_sup_left
    · exact le_sup_right
  let g (a : Bool) : d.X a →* Q := f.comp (inclusion ((hX a).trans (wholeX_le_K c)))
  have hgn : ∃ a, g a ≠ 1 := by
    by_contra hh
    push Not at hh
    apply hfn
    apply hom_eq_one_of_kills_wholeX c f
    have hkill : d.wholeX ≤ f.ker.map c.K.subtype := by
      apply sup_le
      · intro x hx
        refine ⟨⟨x, wholeX_le_K c (hX false hx)⟩, ?_, rfl⟩
        exact DFunLike.congr_fun (hh false) ⟨x, hx⟩
      · intro x hx
        refine ⟨⟨x, wholeX_le_K c (hX true hx)⟩, ?_, rfl⟩
        exact DFunLike.congr_fun (hh true) ⟨x, hx⟩
    intro x
    obtain ⟨y, hy, he⟩ := hkill x.property
    have hey : y = ⟨x, wholeX_le_K c x.property⟩ := Subtype.ext he
    exact MonoidHom.mem_ker.mp (hey ▸ hy)
  obtain ⟨a, ha⟩ := hgn
  obtain ⟨x, hx⟩ := cubic_image_of_nontrivial (c.X_perfect a) (c.X_quotient_card a) (g a) ha
  have hxK : (x : G) ∈ c.K := wholeX_le_K c (hX a x.property)
  have hxprod : (x : G) ∈ (b.first : Set G) * (M : Set G) := b.product_set.symm ▸ hxK
  obtain ⟨l, hl, m, hm, he⟩ := hxprod
  have hfx : g a x = QuotientGroup.mk' (pCore 2 b.first) ⟨l, hl⟩ := by
    change f ⟨(x : G), hxK⟩ = _
    have heq : (⟨(x : G), hxK⟩ : c.K) = ⟨l * m, c.K.mul_mem (hLK hl) (hMK hm)⟩ :=
      Subtype.ext he.symm
    rw [heq]
    exact hflm ⟨l, hl⟩ ⟨m, hm⟩
  refine ⟨⟨x, hX a x.property⟩, ⟨l, hl⟩, hfx ▸ hx, ?_⟩
  intro u
  change (x : G) * ((u : b.first) : G) * (x : G)⁻¹ =
    l * ((u : b.first) : G) * l⁻¹
  rw [← he]
  have hmu := mem_centralizer_iff.mp (hLM (u : b.first).property) m hm
  calc
    (l * m) * ((u : b.first) : G) * (l * m)⁻¹ =
        l * (m * ((u : b.first) : G) * m⁻¹) * l⁻¹ := by
      simp only [mul_inv_rev, mul_assoc]
    _ = l * ((u : b.first) : G) * l⁻¹ := by rw [hmu, mul_inv_cancel_right]

/-- The source normalization and action obligations reduce to block commutation. -/
theorem normalization_and_cubic_actor_of_commuting
    (c : ContraryData κ d i j) (b : ExchangedBlock c)
    (hcomm : ⁅b.first, b.first.map (MulAut.conj b.exchanger).toMonoidHom⁆ = ⊥) :
    d.wholeX ≤ normalizer (b.first : Set G) ∧ HasCubicActor c b :=
  ⟨normalizes_first_of_commuting c b hcomm, hasCubicActor_of_commuting c b hcomm⟩

/-- The actual exchanged blocks supply source normalization and a cubic actor.
Their commutation follows from the relative subnormal block hypotheses. -/
theorem normalization_and_cubic_actor
    (c : ContraryData κ d i j) (b : ExchangedBlock c) :
    d.wholeX ≤ normalizer (b.first : Set G) ∧ HasCubicActor c b :=
  normalization_and_cubic_actor_of_commuting c b (exchanged_blocks_commute c b)

/-- Both source-action inputs for the surviving `L₂(4)` block in 15.4.20. -/
theorem fieldFour_normalization_and_cubic_actor
    (c : ContraryData κ d i j) (b : ExchangedBlock c) (hn : b.n = 2) :
    d.wholeX ≤ normalizer (b.first : Set G) ∧ HasCubicActor c b :=
  normalization_and_cubic_actor_of_commuting c b (fieldFour_exchanged_blocks_commute c b hn)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.FieldFourCentrality
