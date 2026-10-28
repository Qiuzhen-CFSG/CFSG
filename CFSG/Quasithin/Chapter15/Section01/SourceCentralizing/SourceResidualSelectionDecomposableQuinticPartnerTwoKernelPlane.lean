module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoKernelLines
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoFixedLine
public import Theory.GroupTheory.KleinFourLines
public import Theory.GroupTheory.WeakClosureQuotientFusion

/-!
# The original marked kernel plane controls its full normalizer

The two canonical kernel lines generate a four-group. The original Sylow
support exchange fixes their product, which is the actual central partner
involution. Thompson weak closure corrects any normalizer of this four-group
into M modulo its centralizer. Original support permutation then forces it
to fix the same product, putting the full normalizer in Mc.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem conj_generator_of_two_lines
    {A B : Subgroup G} (hB : Nat.card B = 2) {a b g : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) (hb : b ∈ B) (hb1 : b ≠ 1)
    (hm : A.map (MulAut.conj g).toMonoidHom = B) : g*a*g⁻¹ = b := by
  have hmem : g*a*g⁻¹ ∈ B := hm ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom ha
  have hne : g*a*g⁻¹ ≠ 1 := by
    intro he
    apply ha1
    exact (MulAut.conj g).injective (he.trans (map_one (MulAut.conj g)).symm)
  exact congrArg Subtype.val (((Nat.card_eq_two_iff' (1 : B)).mp hB).unique
    (show (⟨g*a*g⁻¹,hmem⟩ : B) ≠ 1 from fun he => hne (congrArg Subtype.val he))
    (show (⟨b,hb⟩ : B) ≠ 1 from fun he => hb1 (congrArg Subtype.val he)))

omit [Finite G] in
private theorem fixes_product_of_permutes_two_lines
    {A B : Subgroup G} (hA : Nat.card A = 2) (hB : Nat.card B = 2)
    {a b g : G} (ha : a ∈ A) (ha1 : a ≠ 1) (hb : b ∈ B) (hb1 : b ≠ 1)
    (hab : a*b=b*a)
    (hp : (A.map (MulAut.conj g).toMonoidHom=A ∧ B.map (MulAut.conj g).toMonoidHom=B) ∨
      (A.map (MulAut.conj g).toMonoidHom=B ∧ B.map (MulAut.conj g).toMonoidHom=A)) :
    g*(a*b)*g⁻¹ = a*b := by
  have hm : g*(a*b)*g⁻¹ = (g*a*g⁻¹)*(g*b*g⁻¹) := by group
  rw [hm]
  rcases hp with hp | hp
  · rw [conj_generator_of_two_lines hA ha ha1 ha ha1 hp.1,
      conj_generator_of_two_lines hB hb hb1 hb hb1 hp.2]
  · rw [conj_generator_of_two_lines hB ha ha1 hb hb1 hp.1,
      conj_generator_of_two_lines hA hb hb1 ha ha1 hp.2,hab]

omit [Finite G] in
private theorem two_axes_intersection
    (A B V₁ V₂ : Subgroup G) (hA : A≤V₁) (hB : B≤V₂)
    (hd : V₁⊓V₂=⊥) (hn : B≤normalizer (A:Set G)) : (A⊔B)⊓V₁=A := by
  apply le_antisymm ?_ (le_inf le_sup_left hA)
  intro x hx
  have hm : x∈(A:Set G)*(B:Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left A B hn]
    exact hx.1
  obtain ⟨a,ha,b,hb,rfl⟩ := hm
  have hb₁ : b∈V₁ := by
    have hh := V₁.mul_mem (V₁.inv_mem (hA ha)) hx.2
    simpa only [inv_mul_cancel_left] using hh
  have hb0 : b=1 := mem_bot.mp (hd ▸ ⟨hb₁,hB hb⟩)
  change a*b∈A
  rw [hb0,mul_one]
  exact ha

/-- The actual kernel four-group has the original partner fixed line and
its full ambient normalizer lies in the original partner Mc. -/
theorem PreparedChosenModule.decomposable_five_partner_two_kernel_plane_normalizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc) = 2 →
      let E := thompsonFixed T V
      let C := centralizer (localModule T Mc : Set G)
      let F := conjugateSpanBy E C
      let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
      let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
      let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
      let J := (D ⊓ Z₁) ⊔ (D ⊓ Z₂)
      V ≤ Mc.pCoreIn 2 ∨
        (Nat.card J = 4 ∧ J ≤ D ⊓ E ∧ (T : Subgroup G) ≤ normalizer (J : Set G) ∧
          localModule T Mc ≤ J ∧ J ⊓ centralizer (T : Set G) = localModule T Mc ∧
          ¬J ≤ centralizer (T : Set G) ∧ normalizer (J : Set G) ≤ Mc) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let E := thompsonFixed T V
  let Uc := localModule T Mc
  let C := centralizer (Uc : Set G)
  let F := conjugateSpanBy E C
  let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
  let V₁ := plane V (c.ambientFactor d s.first).space
  let V₂ := plane V (c.ambientFactor d s.second).space
  let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
  let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
  let D₁ := D⊓Z₁
  let D₂ := D⊓Z₂
  let J := D₁⊔D₂
  by_cases hVQ : V≤Mc.pCoreIn 2
  · exact Or.inl hVQ
  right
  obtain ⟨hc₁,hc₂⟩ := (h.decomposable_five_partner_two_core_or_kernel_lines
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ
  change Nat.card D₁=2 at hc₁
  change Nat.card D₂=2 at hc₂
  obtain ⟨_,_,_,hnD,_⟩ := (h.decomposable_five_partner_two_core_or_canonical_action
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ
  obtain ⟨hUZ,hMcEq,hfixed,_,_⟩ := h.decomposable_five_partner_two_fixed_line
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  have hTMc : (T:Subgroup G)≤Mc := by
    rw [hMcEq]
    exact le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T)
  have hJD : J≤D := sup_le inf_le_left inf_le_left
  have hJE : J≤E := sup_le (inf_le_right.trans inf_le_right) (inf_le_right.trans inf_le_right)
  have hJV : J≤V := hJE.trans inf_le_left
  have hEF : E≤F := le_conjugateSpanBy E C
  have hJF : J≤F := hJE.trans hEF
  have hD₁V : D₁≤V := le_sup_left.trans hJV
  have hD₂V : D₂≤V := le_sup_right.trans hJV
  have hcomm : D₂≤centralizer (D₁:Set G) :=
    hD₂V.trans (V.le_centralizer.trans (centralizer_le hD₁V))
  have hdis : Disjoint D₁ D₂ := disjoint_iff_inf_le.mpr (fun x hx =>
    s.thompson_disjoint.le ⟨hx.1.2,hx.2.2⟩)
  have hcJ : Nat.card J=4 := by
    rw [show J=D₁⊔D₂ from rfl,card_sup_eq_mul_of_normalizes_of_disjoint _ _
      (hcomm.trans (Subgroup.centralizer_le_normalizer _)) hdis,hc₁,hc₂]
  have hTperm (t:G) (ht:t∈(T:Subgroup G)) :
      (D₁.map (MulAut.conj t).toMonoidHom=D₁ ∧ D₂.map (MulAut.conj t).toMonoidHom=D₂) ∨
      (D₁.map (MulAut.conj t).toMonoidHom=D₂ ∧ D₂.map (MulAut.conj t).toMonoidHom=D₁) := by
    have hDm := mem_normalizer_iff_map_conj_eq.mp (hnD (hTMc ht))
    by_cases hn:t∈normalizer (V₁:Set G)
    · have hz:=s.thompson_normalized ⟨ht,hn⟩
      left
      constructor
      · exact (map_inf _ _ _ (MulAut.conj t).injective).trans
          (congrArg₂ (·⊓·) hDm (mem_normalizer_iff_map_conj_eq.mp hz.1))
      · exact (map_inf _ _ _ (MulAut.conj t).injective).trans
          (congrArg₂ (·⊓·) hDm (mem_normalizer_iff_map_conj_eq.mp hz.2))
    · have hz:=s.thompson_exchanges t ht hn
      right
      exact ⟨(map_inf _ _ _ (MulAut.conj t).injective).trans (congrArg₂ (·⊓·) hDm hz.1),
        (map_inf _ _ _ (MulAut.conj t).injective).trans (congrArg₂ (·⊓·) hDm hz.2)⟩
  have hTJ : (T:Subgroup G)≤normalizer (J:Set G) := by
    intro t ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (D₁⊔D₂).map (MulAut.conj t).toMonoidHom=D₁⊔D₂
    rw [Subgroup.map_sup]
    rcases hTperm t ht with hh|hh
    · rw [hh.1,hh.2]
    · rw [hh.1,hh.2,sup_comm]
  obtain ⟨a,ha,ha1,_⟩ := exists_generator_of_card_two D₁ hc₁
  obtain ⟨b,hb,hb1,_⟩ := exists_generator_of_card_two D₂ hc₂
  have hab : a*b=b*a := hcomm hb a ha
  have huJ : a*b∈J := J.mul_mem ((show D₁≤J from le_sup_left) ha) ((show D₂≤J from le_sup_right) hb)
  have hu1 : a*b≠1 := by
    intro he
    have hae : a=b⁻¹ := mul_eq_one_iff_eq_inv.mp he
    exact ha1 (disjoint_def.mp hdis ha (hae ▸ D₂.inv_mem hb))
  have huT : a*b∈centralizer (T:Set G) := by
    intro t ht
    exact mul_inv_eq_iff_eq_mul.mp (fixes_product_of_permutes_two_lines hc₁ hc₂
      ha ha1 hb hb1 hab (hTperm t ht))
  have huU : a*b∈Uc := hfixed.le ⟨hJF huJ,huT⟩
  have hzU : zpowers (a*b)=Uc := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr huU)
    have hh := (one_lt_card_iff_ne_bot (zpowers (a*b))).mpr (by
      intro hz
      exact hu1 (mem_bot.mp (hz ▸ mem_zpowers (a*b))))
    change Nat.card Uc=2 at hcU
    omega
  have hUJ : Uc≤J := hzU ▸ zpowers_le.mpr huJ
  have hfixJ : J⊓centralizer (T:Set G)=Uc := le_antisymm
    ((inf_le_inf_right _ hJF).trans_eq hfixed)
    (le_inf hUJ (hUZ.le.trans (centralInvolutions_le_centralizer_sylow T)))
  have hncent : ¬J≤centralizer (T:Set G) := by
    intro hh
    have hj : J≤Uc := (le_inf le_rfl hh).trans_eq hfixJ
    have hc := card_le_of_le hj
    rw [hcJ,hcU] at hc
    omega
  refine ⟨hcJ,le_inf hJD hJE,hTJ,hUJ,hfixJ,hncent,?_⟩
  have hJ₁ : J⊓V₁=D₁ := two_axes_intersection D₁ D₂ V₁ V₂
    (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_left) s.disjoint
    (hcomm.trans (Subgroup.centralizer_le_normalizer _))
  have hJ₂ : J⊓V₂=D₂ := by
    rw [show J=D₂⊔D₁ from sup_comm D₁ D₂]
    exact two_axes_intersection D₂ D₁ V₂ V₁
      (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_left)
      (inf_comm V₂ V₁ ▸ s.disjoint)
      ((le_centralizer_iff.mp hcomm).trans (Subgroup.centralizer_le_normalizer _))
  intro g hg
  let JT := elementaryAbelianMaxJ (T:Subgroup G)
  let CJ := centralizer (J:Set G)
  have hJT : JT≤CJ := (hJ.trans (centralizer_le h.le_local)).trans (centralizer_le hJV)
  have hgJT : JT.map (MulAut.conj g).toMonoidHom≤CJ := (map_mono hJT).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp ((normalizer_le_normalizer_centralizer J) hg))
  obtain ⟨k,hk⟩ := Sylow.WeakClosure.normalizer_correction T JT
    (sSup_le fun _ hA=>hA.1) (maxJ_weakly_closed_normalizer T) CJ hJT g hgJT
  let n := (k:G)*g
  have hnM : n∈M := (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1 hk
  have hnJ : n∈normalizer (J:Set G) := (normalizer (J:Set G)).mul_mem
    ((Subgroup.centralizer_le_normalizer _) k.property) hg
  let y:M := ⟨n,hnM⟩
  let f := (actionHom M V h.normalized).rangeRestrict
  have hplanes (i:d.Index) : (plane V (c.ambientFactor d i).space).map
      (MulAut.conj n).toMonoidHom=plane V (c.ambientFactor d (π (f y) i)).space :=
    (plane_conjugate h.normalized _ y).trans (congrArg (plane V) (hs (f y) i))
  have hperm : (π (f y) s.first=s.first ∧ π (f y) s.second=s.second) ∨
      (π (f y) s.first=s.second ∧ π (f y) s.second=s.first) := by
    rcases s.covers (π (f y) s.first) with hi|hi
    · left
      refine ⟨hi,?_⟩
      rcases s.covers (π (f y) s.second) with hj|hj
      · exact (s.distinct ((π (f y)).injective (hi.trans hj.symm))).elim
      · exact hj
    · right
      refine ⟨hi,?_⟩
      rcases s.covers (π (f y) s.second) with hj|hj
      · exact hj
      · exact (s.distinct ((π (f y)).injective (hi.trans hj.symm))).elim
  have hJm : J.map (MulAut.conj n).toMonoidHom=J := mem_normalizer_iff_map_conj_eq.mp hnJ
  have hDi : (D₁.map (MulAut.conj n).toMonoidHom=D₁ ∧ D₂.map (MulAut.conj n).toMonoidHom=D₂) ∨
      (D₁.map (MulAut.conj n).toMonoidHom=D₂ ∧ D₂.map (MulAut.conj n).toMonoidHom=D₁) := by
    rw [←hJ₁,←hJ₂,map_inf _ _ _ (MulAut.conj n).injective,
      map_inf _ _ _ (MulAut.conj n).injective,hJm,hplanes s.first,hplanes s.second]
    rcases hperm with hh|hh
    · exact Or.inl ⟨by rw [hh.1],by rw [hh.2]⟩
    · exact Or.inr ⟨by rw [hh.1],by rw [hh.2]⟩
  have hnfix := fixes_product_of_permutes_two_lines hc₁ hc₂ ha ha1 hb hb1 hab hDi
  have hgfix : g*(a*b)*g⁻¹=a*b := by
    calc
      g*(a*b)*g⁻¹=(k:G)⁻¹*(n*(a*b)*n⁻¹)*(k:G) := by dsimp [n]; group
      _=(k:G)⁻¹*(a*b)*(k:G) := by rw [hnfix]
      _=a*b := by rw [mul_assoc,k.property _ huJ,inv_mul_cancel_left]
  have hgU : g∈centralizer (Uc:Set G) := by
    rw [←hzU,zpowers_eq_closure,centralizer_closure,mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp hgfix
  rw [hMcEq,←hUZ]
  exact hgU

end CFSG.Quasithin.Chapter15.Section01
