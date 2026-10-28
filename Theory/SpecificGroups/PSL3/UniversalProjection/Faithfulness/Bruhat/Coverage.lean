module

public import Theory.SpecificGroups.PSL3.UniversalProjection.Faithfulness.Bruhat.Upper
public import Theory.SpecificGroups.PSL3.UniversalProjection.Faithfulness.Bruhat.Coverage.RootTransport

/-!
# Bruhat coverage in the degree-three Steinberg presentation

Positive roots and simple Weyl words generate the presentation. Factor the
right upper term along a simple root and its complement. Conjugation moves
the complement past the simple Weyl word. Root transport then absorbs the
remaining factor into the left upper term, or rank-one exchange replaces it
by an opposite root whose transported image is positive. Word induction
therefore proves `G = U N U` for the literal generated subgroups.

Torus multiplicativity is unnecessary for coverage; the requested version
retains that premise for the existing kernel-reduction interface. The
upper, Weyl and torus subgroups are never replaced by matrix preimages.

Source: GLS3 §2.9, printed pp.97–98; Steinberg, *Lectures on Chevalley
Groups*, §§3 and 6, Lemmas 36–37 and Theorem 8, printed pp.69–71.
-/

@[expose] public section

namespace Matrix.PSL3.UniversalProjection.Faithfulness
open Theory.SpecificGroups.LinearHigher SteinbergWords
open PositiveCollection
variable {F : Type*} [Field F]

namespace PositiveCollection

private theorem swap_simple_positive (k : Fin 2) (r : Root 3)
    (hr : r.val.1 < r.val.2) (hne : r ≠ simpleRoot k) :
    (permuteRoot (Equiv.swap k.castSucc k.succ) r).val.1 <
      (permuteRoot (Equiv.swap k.castSucc k.succ) r).val.2 := by
  revert r k
  decide

private theorem simple_conj_complement (k : Fin 2) (t : Fˣ) {v : SteinbergGroup 3 F}
    (hv : v ∈ complement (F := F) k) :
    MulAut.conj (weylWord generator (simpleRoot k).val.1 (simpleRoot k).val.2 (simpleRoot k).property t) v ∈
      upperSubgroup F := by
  induction hv using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨r,a,hr,hne,rfl⟩ := hg
    obtain ⟨c,hc⟩ := weylWord_transport (simpleRoot k).val.1 (simpleRoot k).val.2 (simpleRoot k).property t r
    rw [hc]
    exact generator_mem_upper (swap_simple_positive k r hr hne) _
  | one => simpa only [map_one] using (upperSubgroup F).one_mem
  | mul x y _ _ hx hy => simpa only [map_mul] using (upperSubgroup F).mul_mem hx hy
  | inv x _ hx => simpa only [map_inv] using (upperSubgroup F).inv_mem hx

private def collectionGenerators : Set (SteinbergGroup 3 F) :=
  {g | ∃ (r : Root 3) (a : F), r.val.1 < r.val.2 ∧ g = generator r a} ∪
  {g | ∃ (k : Fin 2) (t : Fˣ),
    g = weylWord generator (simpleRoot k).val.1 (simpleRoot k).val.2 (simpleRoot k).property t}

private theorem closure_collectionGenerators :
    Subgroup.closure (collectionGenerators (F := F)) = ⊤ := by
  let H := Subgroup.closure (collectionGenerators (F := F))
  have hpos (r : Root 3) (hr : r.val.1 < r.val.2) (a : F) : generator r a ∈ H :=
    Subgroup.subset_closure (Or.inl ⟨r,a,hr,rfl⟩)
  have hw (k : Fin 2) (t : Fˣ) :
      weylWord generator (simpleRoot k).val.1 (simpleRoot k).val.2 (simpleRoot k).property t ∈ H :=
    Subgroup.subset_closure (Or.inr ⟨k,t,rfl⟩)
  have hneg (k : Fin 2) (a : F) :
      generator (root (simpleRoot k).val.2 (simpleRoot k).val.1
        (simpleRoot k).property.symm) a ∈ H := by
    have he := weylWord_conj_root generator_relations (by decide)
      (simpleRoot k).val.1 (simpleRoot k).val.2 (simpleRoot k).property (1 : Fˣ) (-a)
    simp only [inv_one, Units.val_one, neg_mul, one_mul, neg_neg, mul_one] at he
    rw [← he]
    exact H.mul_mem (H.mul_mem (hw k 1) (hpos (simpleRoot k) (by
      change k.val < k.val + 1
      omega) (-a))) (H.inv_mem (hw k 1))
  have h20 (a : F) : generator (root (2 : Fin 3) 0 (by decide)) a ∈ H := by
    have he := generator_relations.chain (2 : Fin 3) 1 0
      (by decide) (by decide) (by decide) a (1 : F)
    rw [mul_one] at he
    rw [← he]
    exact H.mul_mem (H.mul_mem (H.mul_mem (hneg 1 a) (hneg 0 1))
      (H.inv_mem (hneg 1 a))) (H.inv_mem (hneg 0 1))
  apply top_unique
  intro g _
  apply PresentedGroup.generated_by _ H _ g
  rintro ⟨⟨⟨i,j⟩,hij⟩,a⟩
  change generator (root i j hij) a ∈ H
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact hpos _ (by dsimp [root]; decide) a
  · exact hpos _ (by dsimp [root]; decide) a
  · exact hneg 0 a
  · exact (hij rfl).elim
  · exact hpos _ (by dsimp [root]; decide) a
  · exact h20 a
  · exact hneg 1 a
  · exact (hij rfl).elim

private def InBruhat (g : SteinbergGroup 3 F) : Prop :=
  ∃ (u : upperSubgroup F) (w : weylSubgroup F) (v : upperSubgroup F),
    g = u.val * w.val * v.val

private theorem inBruhat_mul_upper {g t : SteinbergGroup 3 F}
    (hg : InBruhat g) (ht : t ∈ upperSubgroup F) : InBruhat (g*t) := by
  obtain ⟨u,w,v,rfl⟩ := hg
  exact ⟨u,w,⟨v.val*t,(upperSubgroup F).mul_mem v.property ht⟩,mul_assoc _ _ _⟩

private theorem inBruhat_mul_simple {g : SteinbergGroup 3 F} (hg : InBruhat g)
    (k : Fin 2) (t : Fˣ) :
    InBruhat (g * weylWord generator (simpleRoot k).val.1 (simpleRoot k).val.2 (simpleRoot k).property t) := by
  obtain ⟨u,w,v,hg⟩ := hg
  obtain ⟨a,c,hc⟩ := factor_simple k v.property
  let r := simpleRoot k
  let s : weylSubgroup F := ⟨weylWord generator r.val.1 r.val.2 r.property t,
    weylWord_mem_weyl _ _ _ _⟩
  let d : upperSubgroup F := ⟨MulAut.conj s.val⁻¹ c.val, by
    change MulAut.conj
      (weylWord generator (simpleRoot k).val.1 (simpleRoot k).val.2 (simpleRoot k).property t)⁻¹ c.val ∈ _
    rw [weylWord_inv generator_relations]
    exact simple_conj_complement k (-t) c.property⟩
  have hcs : c.val * s.val = s.val * d.val := by
    dsimp [d]
    group
  have hred : g * s.val = u.val * (w.val * generator r a * s.val) * d.val := by
    rw [hg, hc]
    simp only [mul_assoc, hcs, r]
  change InBruhat (g*s.val)
  by_cases ha : a = 0
  · refine ⟨u,w*s,d,?_⟩
    simpa only [ha, generator_relations.zero, mul_one, Subgroup.coe_mul] using hred
  obtain ⟨σ,hσ⟩ := weyl_transport w.property
  obtain ⟨b,hb⟩ := hσ r
  by_cases hpos : (permuteRoot σ r).val.1 < (permuteRoot σ r).val.2
  · let z : upperSubgroup F := ⟨generator (permuteRoot σ r) ((b : F)*a),
      generator_mem_upper hpos _⟩
    have hz : w.val * generator r a = z.val * w.val :=
      mul_inv_eq_iff_eq_mul.mp (hb a)
    refine ⟨u*z,w*s,d,?_⟩
    rw [hred,hz]
    simp only [Subgroup.coe_mul,mul_assoc]
  · let q := root r.val.2 r.val.1 r.property.symm
    have hq : (permuteRoot σ q).val.1 < (permuteRoot σ q).val.2 := by
      change σ r.val.2 < σ r.val.1
      change ¬σ r.val.1 < σ r.val.2 at hpos
      exact lt_of_le_of_ne (le_of_not_gt hpos) (σ.injective.ne r.property).symm
    let aU : Fˣ := Units.mk0 a ha
    obtain ⟨b',hb'⟩ := hσ q
    let z : upperSubgroup F := ⟨generator (permuteRoot σ q) ((b' : F)*(aU⁻¹ : Fˣ)),
      generator_mem_upper hq _⟩
    let n : weylSubgroup F := ⟨weylWord generator r.val.1 r.val.2 r.property aU,
      weylWord_mem_weyl _ _ _ _⟩
    let x : upperSubgroup F := ⟨generator r (-(t : F)*(aU⁻¹ : Fˣ)*(t : F)),
      generator_mem_upper (by change k.val < k.val+1; omega) _⟩
    have hz : w.val * generator q ((aU⁻¹ : Fˣ) : F) = z.val * w.val :=
      mul_inv_eq_iff_eq_mul.mp (hb' _)
    have hex : generator r a * s.val =
        generator q ((aU⁻¹ : Fˣ) : F) * (n.val*s.val) * x.val :=
      rank_one_exchange r.val.1 r.val.2 r.property aU t
    refine ⟨u*z,w*n*s,x*d,?_⟩
    rw [hred, mul_assoc w.val, hex]
    rw [← mul_assoc w.val, ← mul_assoc w.val, hz]
    simp only [Subgroup.coe_mul,mul_assoc]
end PositiveCollection

/-- Every element of the presentation belongs to `U N U`, over any field. -/
theorem bruhatCover : BruhatCover F := by
  intro g
  have hg : g ∈ Subgroup.closure (collectionGenerators (F := F)) := by
    rw [closure_collectionGenerators]
    trivial
  change InBruhat g
  have step (g y : SteinbergGroup 3 F) (hg : InBruhat g)
      (hy : y ∈ collectionGenerators (F := F)) : InBruhat (g*y) := by
    rcases hy with ⟨r,a,hr,rfl⟩ | ⟨k,t,rfl⟩
    · exact inBruhat_mul_upper hg (generator_mem_upper hr a)
    · exact inBruhat_mul_simple hg k t
  induction hg using Subgroup.closure_induction_right with
  | one => exact ⟨1,1,1,by simp⟩
  | mul_right g _ y hy ih => exact step g y ih hy
  | mul_inv_cancel g _ y hy ih =>
    rcases hy with ⟨r,a,hr,rfl⟩ | ⟨k,t,rfl⟩
    · rw [← generator_relations.neg]
      exact inBruhat_mul_upper ih (generator_mem_upper hr (-a))
    · rw [weylWord_inv generator_relations]
      exact inBruhat_mul_simple ih k (-t)

/-- The Bruhat input with the premise used by the kernel-reduction consumer. -/
theorem bruhatCover_of_torusMultiplicative (_hC : TorusMultiplicative F) : BruhatCover F :=
  bruhatCover
end Matrix.PSL3.UniversalProjection.Faithfulness
