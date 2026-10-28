module
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterCentralizerGeneration
public import Theory.SpecificGroups.PSL3Two.Parabolics.PointNormalizer
public import Theory.GroupTheory.GeneralizedFitting.SquareWreath
public import Theory.GroupTheory.RegularWreathSubgroup
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# Solvable Sylow overgroups of a binary linear-three square

A solvable subgroup of SL₃(2) × SL₃(2) containing a Sylow two-subgroup
and with order divisible by nine is a product of two parabolics. Each
projection lies in a parabolic of order 24; divisibility by 64 and nine
forces equality with their product. Independent factor markings identify
both parabolics with the standard line stabilizer.

Automorphisms preserving this marked product have inner coordinate maps,
since preserving a line parabolic excludes the graph automorphism. Thus a
self-centralizing normal square with two-group quotient and a solvable
Sylow overgroup containing a cubic plane embeds in SL₃(2) wr C₂. If the
square is proper, the embedding is surjective. The strengthened marking also
identifies the original solvable overgroup with the line-parabolic wreath,
which is needed to apply the radical normalizer theorem. The Chapter14 application
uses the actual H-image and the original inverse exchanger.

Source: Aschbacher--Smith 14.6.14(3), printed p.1033; I.5.3--4 for the
binary parabolics. The imported matrix models retain ATLAS attribution
and license, LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Matrix.PSL3Two.SquareParabolic

private theorem solvable_marking (S : Sylow 2 SL) (A : Subgroup SL)
    (hs : Group.IsSolvable A) (hSA : (S : Subgroup SL) ≤ A) :
    ∃ e : MulAut SL, A.map e.toMonoidHom ≤ lineParabolicSL := by
  let := Atlas.Comparisons.Exceptional.sl3Two_simple
  let : Group.IsPerfect SL := Atlas.sl_perfect 3 (by decide)
  obtain ⟨e,hS⟩ := exists_sylow_marking equiv S
  let := hs
  let : Group.IsSolvable (A.map e.toMonoidHom) :=
    Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective A)
  have hne : A.map e.toMonoidHom ≠ ⊤ := by
    intro he
    let : Group.IsSolvable (⊤ : Subgroup SL) := he ▸ inferInstanceAs
      (Group.IsSolvable (A.map e.toMonoidHom))
    have hh : Group.IsSolvable SL := Group.isSolvable_of_surjective
      (f := (topEquiv (G := SL)).toMonoidHom) (topEquiv (G := SL)).surjective
    exact Group.IsPerfect.not_isSolvable SL hh
  have hle : borelSL ≤ A.map e.toMonoidHom := hS ▸ map_mono hSA
  rcases overgroup_borelSL _ hle hne with hp | hl
  · refine ⟨e.trans flagDuality,?_⟩
    change A.map (flagDuality.toMonoidHom.comp e.toMonoidHom) ≤ _
    rw [←Subgroup.map_map,←flagDuality_map_point]
    exact map_mono hp
  · exact ⟨e,hl⟩

/-- A solvable Sylow overgroup containing a full cubic plane is the product
of its two parabolic projections, with one actual marking on each factor. -/
theorem solvable_square_marking (S : Sylow 2 (SL × SL)) (A : Subgroup (SL × SL))
    (hs : Group.IsSolvable A) (hSA : (S : Subgroup (SL × SL)) ≤ A)
    (h9 : 9 ∣ Nat.card A) :
    ∃ e₁ e₂ : MulAut SL, A.map (e₁.prodCongr e₂).toMonoidHom =
      lineParabolicSL.prod lineParabolicSL := by
  let := hs
  let f₁ := MonoidHom.fst SL SL
  let f₂ := MonoidHom.snd SL SL
  have hs₁ : Group.IsSolvable (A.map f₁) :=
    Group.isSolvable_of_surjective (f₁.subgroupMap_surjective A)
  have hs₂ : Group.IsSolvable (A.map f₂) :=
    Group.isSolvable_of_surjective (f₂.subgroupMap_surjective A)
  obtain ⟨e₁,he₁⟩ := solvable_marking
    (S.mapSurjective (f := f₁) (fun x => ⟨(x,1),rfl⟩)) _ hs₁ (map_mono hSA)
  obtain ⟨e₂,he₂⟩ := solvable_marking
    (S.mapSurjective (f := f₂) (fun x => ⟨(1,x),rfl⟩)) _ hs₂ (map_mono hSA)
  refine ⟨e₁,e₂,eq_of_le_of_card_ge ?_ ?_⟩
  · rintro _ ⟨x,hx,rfl⟩
    exact ⟨he₁ (mem_map_of_mem _ (mem_map_of_mem f₁ hx)),
      he₂ (mem_map_of_mem _ (mem_map_of_mem f₂ hx))⟩
  · have h64 : 64 ∣ Nat.card A := by
      have hh := card_dvd_of_le hSA
      have hS : Nat.card (S : Subgroup (SL × SL)) = 64 := by
        rw [S.card_eq_multiplicity,Nat.card_prod,card_SL]
        decide +kernel
      rwa [hS] at hh
    have h576 : 576 ∣ Nat.card A := by
      have hh := Nat.lcm_dvd h64 h9
      norm_num at hh
      exact hh
    rw [card_map_of_injective (e₁.prodCongr e₂).injective,
      Nat.card_congr (prodEquiv lineParabolicSL lineParabolicSL).toEquiv,
      Nat.card_prod,card_lineParabolicSL]
    exact Nat.le_of_dvd Nat.card_pos h576

/-- Preserving the actual line parabolic excludes diagram action. -/
theorem inner_of_line_preserving (a : MulAut SL)
    (ha : lineParabolicSL.map a.toMonoidHom = lineParabolicSL) :
    a ∈ MulAut.innerSubgroup SL := by
  have hr := map_embedded_pResidual 2 lineParabolicSL a.toMonoidHom
  change (MarkedAutomorphisms.residual lineParabolicSL).map a.toMonoidHom =
    MarkedAutomorphisms.residual (lineParabolicSL.map a.toMonoidHom) at hr
  rw [ha,MarkedAutomorphisms.line_residual] at hr
  obtain ⟨g,_,hg⟩ := MarkedAutomorphisms.line_implementer a (by
    intro x hx
    rw [←hr]
    exact mem_map_of_mem _ hx)
  exact ⟨g,hg.symm⟩



open AutomorphismSquare WreathTwoElementaryRank

/-- The stabilizer of the two marked line parabolics has inner coordinate
maps, including when its two factors are interchanged. -/
theorem wreath_inner_of_parabolic_preserving (w : W (MulAut SL))
    (hw : (lineParabolicSL.prod lineParabolicSL).map
      (wreathHom w).toMonoidHom = lineParabolicSL.prod lineParabolicSL) :
    w ∈ RegularWreathProduct.coordinateSubgroup (MulAut.innerSubgroup SL) := by
  have hh (x : SL × SL) (hx : x ∈ lineParabolicSL.prod lineParabolicSL) :
      wreathHom w x ∈ lineParabolicSL.prod lineParabolicSL :=
    hw ▸ mem_map_of_mem _ hx
  have ha : ∀ i, ∀ x ∈ lineParabolicSL, w.left i x ∈ lineParabolicSL := by
    intro i x hx
    rcases index_cases i with rfl | rfl <;>
      by_cases h : w.right = 1
    · have hh' := (hh (x,1) ⟨hx,one_mem _⟩).1
      change (wreathMap w (x,1)).1 ∈ lineParabolicSL at hh'
      simpa only [wreathMap_apply,h,ite_true] using hh'
    · have hh' := (hh (1,x) ⟨one_mem _,hx⟩).1
      change (wreathMap w (1,x)).1 ∈ lineParabolicSL at hh'
      simpa only [wreathMap_apply,h,ite_false] using hh'
    · have hh' := (hh (1,x) ⟨one_mem _,hx⟩).2
      change (wreathMap w (1,x)).2 ∈ lineParabolicSL at hh'
      simpa only [wreathMap_apply,h,ite_true] using hh'
    · have hh' := (hh (x,1) ⟨hx,one_mem _⟩).2
      change (wreathMap w (x,1)).2 ∈ lineParabolicSL at hh'
      simpa only [wreathMap_apply,h,ite_false] using hh'
  intro i
  apply inner_of_line_preserving
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x,hx,rfl⟩
    exact ha i x hx
  · rw [card_map_of_injective (w.left i).injective]

/-- The literal inner-coordinate wreath is the wreath of the original
centerless matrix group. -/
def innerWreathEquiv :
    RegularWreathProduct.coordinateSubgroup (Q := C2) (MulAut.innerSubgroup SL) ≃* W SL :=
  (RegularWreathProduct.coordinateSubgroupEquiv (MulAut.innerSubgroup SL)).trans
    (RegularWreathProduct.congr
      (MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot center_eq_bot)).symm
      (MulEquiv.refl C2))

variable {Q : Type*} [Group Q] [Finite Q]

/-- The cubic plane in a solvable Sylow overgroup survives intersection with
a normal subgroup whose quotient is a two-group. -/
theorem nine_dvd_intersection (N B : Subgroup Q) [N.Normal]
    (hq : IsPGroup 2 (Q ⧸ N)) (h9 : 9 ∣ Nat.card B) :
    9 ∣ Nat.card (B.subgroupOf N) := by
  let f := (QuotientGroup.mk' N).comp B.subtype
  have hp : IsPGroup 2 f.range := hq.to_subgroup _
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hker : Nat.card f.ker = Nat.card (B.subgroupOf N) := by
    have hk : f.ker = N.subgroupOf B := by
      change ((QuotientGroup.mk' N).comp B.subtype).ker = _
      rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
      rfl
    rw [hk,←card_map_of_injective B.subtype_injective,
      subgroupOf_map_subtype,←card_map_of_injective N.subtype_injective,
      subgroupOf_map_subtype,inf_comm]
  have hh : 9 ∣ Nat.card f.ker * 2^n := by
    rw [←hn,←index_ker, f.ker.card_mul_index]
    exact h9
  have hd := ((show Nat.Coprime 9 2 by decide).pow_right n).dvd_of_dvd_mul_right hh
  rwa [hker] at hd



private def markedCoordinateEquiv :
    RegularWreathProduct.coordinateSubgroup (Q := C2) (MulAut.innerSubgroup SL) ≃*
      W (MulAut.innerSubgroup SL) where
  toFun w := ⟨fun i => ⟨w.val.left i,w.property i⟩,w.val.right⟩
  invFun w := ⟨⟨fun i => (w.left i).val,w.right⟩,fun i => (w.left i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private def markedInnerWreathEquiv :
    RegularWreathProduct.coordinateSubgroup (Q := C2) (MulAut.innerSubgroup SL) ≃* W SL :=
  markedCoordinateEquiv.trans (RegularWreathProduct.congr
    (MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot center_eq_bot)).symm
    (MulEquiv.refl C2))

private theorem markedInnerWreathEquiv_coordinate
    (w : RegularWreathProduct.coordinateSubgroup (Q := C2) (MulAut.innerSubgroup SL)) (i : C2) :
    MulAut.conj ((markedInnerWreathEquiv w).left i) = w.val.left i := by
  change MulAut.conj ((MonoidHom.ofInjective
    (MulAut.conj_injective_of_center_eq_bot center_eq_bot)).symm
    ⟨w.val.left i,w.property i⟩) = w.val.left i
  exact MonoidHom.apply_ofInjective_symm _ _

private theorem markedInnerWreathEquiv_parabolic
    (w : RegularWreathProduct.coordinateSubgroup (Q := C2) (MulAut.innerSubgroup SL))
    (hw : (lineParabolicSL.prod lineParabolicSL).map (wreathHom w.val).toMonoidHom =
      lineParabolicSL.prod lineParabolicSL) : markedInnerWreathEquiv w ∈ (RegularWreathProduct.coordinateSubgroup (Q := C2) lineParabolicSL) := by
  intro i
  have hn : normalizer (lineParabolicSL : Set SL) = lineParabolicSL := by
    rw [←MarkedAutomorphisms.pointParabolic_map_diagram,←map_equiv_normalizer_eq,
      pointParabolicSL_normalizer]
  rw [←hn]
  apply mem_normalizer_fintype
  intro x hx
  have hh := hw ▸ mem_map_of_mem (wreathHom w.val).toMonoidHom
    (show (x,x) ∈ lineParabolicSL.prod lineParabolicSL from ⟨hx,hx⟩)
  change (wreathMap w.val (x,x)).1 ∈ lineParabolicSL ∧
    (wreathMap w.val (x,x)).2 ∈ lineParabolicSL at hh
  rw [wreathMap_apply] at hh
  have ht : w.val.left i x ∈ lineParabolicSL := by
    rcases index_cases i with rfl | rfl
    · split_ifs at hh <;> exact hh.1
    · split_ifs at hh <;> exact hh.2
  change (MulAut.conj ((markedInnerWreathEquiv w).left i)) x ∈ lineParabolicSL
  rwa [markedInnerWreathEquiv_coordinate]

/-- The full wreath identification also marks the given solvable Sylow
overgroup as the literal line parabolic wreath. -/
theorem full_wreath_marking_of_solvable_overgroup
    (N B : Subgroup Q) [N.Normal] (e : N ≃* SL × SL)
    (hc : centralizer (N : Set Q) = ⊥) (hq : IsPGroup 2 (Q ⧸ N))
    (T : Sylow 2 Q) (hgen : N ⊔ (T : Subgroup Q) = ⊤)
    (hTB : (T : Subgroup Q) ≤ B) (hB : Group.IsSolvable B)
    (h9 : 9 ∣ Nat.card B) (hne : N ≠ ⊤) : ∃ E : Q ≃* W SL, B.map E.toMonoidHom = (RegularWreathProduct.coordinateSubgroup (Q := C2) lineParabolicSL) := by
  let := Atlas.Comparisons.Exceptional.sl3Two_simple
  let : Group.IsPerfect SL := Atlas.sl_perfect 3 (by decide)
  let : IsQuasisimple SL := {
    simple := ((QuotientGroup.quotientMulEquivOfEq center_eq_bot).trans
      QuotientGroup.quotientBot).isSimpleGroup }
  obtain ⟨S,hS⟩ := T.exists_subgroupOf_eq_of_normal N
  let A := (B.subgroupOf N).map e.toMonoidHom
  let f : B.subgroupOf N →* B := {
    toFun x := ⟨x.val.val,x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : B => (z : Q)) h))
  let := hB
  let : Group.IsSolvable (B.subgroupOf N) := Group.isSolvable_of_isSolvable_injective hf
  have hs : Group.IsSolvable A := Group.isSolvable_of_surjective
    (e.toMonoidHom.subgroupMap_surjective _)
  have hSA : (S.mapSurjective (f := e.toMonoidHom) e.surjective : Subgroup (SL × SL)) ≤ A := by
    apply map_mono
    rw [hS]
    exact subgroupOf_mono N hTB
  have h9A : 9 ∣ Nat.card A := by
    rw [card_map_of_injective e.injective]
    exact nine_dvd_intersection N B hq h9
  obtain ⟨a,b,hab⟩ := solvable_square_marking
    (S.mapSurjective (f := e.toMonoidHom) e.surjective) A hs hSA h9A
  let k := e.trans (a.prodCongr b)
  have hmark : (B.subgroupOf N).map k.toMonoidHom = lineParabolicSL.prod lineParabolicSL := by
    change (B.subgroupOf N).map ((a.prodCongr b).toMonoidHom.comp e.toMonoidHom) = _
    rw [←Subgroup.map_map]
    exact hab
  let r := wreathConjugation N k center_eq_bot
  let I := RegularWreathProduct.coordinateSubgroup (Q := C2) (MulAut.innerSubgroup SL)
  have hpres (g : Q) (hg : g ∈ B) :
      (lineParabolicSL.prod lineParabolicSL).map (wreathHom (r g)).toMonoidHom =
        lineParabolicSL.prod lineParabolicSL := by
    have hwr : wreathHom (r g) = squareConjugation N k g :=
      (wreathEquiv center_eq_bot).apply_symm_apply _
    rw [hwr,←hmark,Subgroup.map_map]
    have he : (squareConjugation N k g).toMonoidHom.comp k.toMonoidHom =
        k.toMonoidHom.comp (MulAut.conjNormal g).toMonoidHom := by
      apply MonoidHom.ext
      intro x
      change k ((MulAut.conjNormal g) (k.symm (k x))) = k ((MulAut.conjNormal g) x)
      rw [k.symm_apply_apply]
    rw [he,←Subgroup.map_map]
    have hstable : (B.subgroupOf N).map (MulAut.conjNormal g).toMonoidHom = B.subgroupOf N := by
      apply eq_of_le_of_card_ge
      · rintro _ ⟨x,hx,rfl⟩
        exact B.mul_mem (B.mul_mem hg hx) (B.inv_mem hg)
      · rw [card_map_of_injective (f := (MulAut.conjNormal g : MulAut N).toMonoidHom)
          (MulAut.conjNormal g : MulAut N).injective]
    rw [hstable]
  have hBI : B ≤ I.comap r := fun g hg =>
    wreath_inner_of_parabolic_preserving _ (hpres g hg)
  have hNI : N ≤ I.comap r := by
    intro x hx
    have hh := wreathConjugation_inner N k center_eq_bot ⟨x,hx⟩
    change r x ∈ I
    rw [hh]
    intro i
    rcases index_cases i with rfl | rfl
    · exact ⟨(k ⟨x,hx⟩).1,by simp [baseHom]⟩
    · exact ⟨(k ⟨x,hx⟩).2,by simp [baseHom,turn_ne_one]⟩
  have hall : I.comap r = ⊤ := top_unique (hgen ▸ sup_le hNI (hTB.trans hBI))
  let f := markedInnerWreathEquiv.toMonoidHom.comp (r.codRestrict I (fun x => (show x ∈ I.comap r from hall ▸ mem_top x)))
  have hi : Function.Injective f := markedInnerWreathEquiv.injective.comp
    (fun _ _ h => wreathConjugation_injective N k center_eq_bot hc (congrArg Subtype.val h))
  have hNc : Nat.card N = 28224 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_prod,card_SL]
  have hWc : Nat.card (W SL) = 56448 := by
    rw [RegularWreathProduct.card,card_SL]
    norm_num [C2,Nat.card_eq_fintype_card]
  have hncard : Nat.card N < Nat.card Q := by
    have hh := card_le_card_group N
    exact lt_of_le_of_ne hh (fun he => hne (N.eq_top_of_card_eq he))
  have hd : Nat.card Q ∣ 56448 := hWc ▸ card_dvd_of_injective f hi
  have he : 56448 = Nat.card Q := Nat.eq_of_dvd_of_lt_two_mul (by decide) hd (by
    rw [hNc] at hncard
    omega)
  let E := MulEquiv.ofBijective f (hi.bijective_of_nat_card_le (by omega))
  refine ⟨E,eq_of_le_of_card_ge ?_ ?_⟩
  · rintro _ ⟨g,hg,rfl⟩
    exact markedInnerWreathEquiv_parabolic ⟨r g,show g ∈ I.comap r from hall ▸ mem_top g⟩ (hpres g hg)
  · have h128 : 128 ∣ Nat.card B := by
      have hh := card_dvd_of_le hTB
      have ht : Nat.card T = 128 := by
        rw [T.card_eq_multiplicity,←he]
        decide +kernel
      rwa [ht] at hh
    have h1152 : 1152 ∣ Nat.card B := by
      have hh := Nat.lcm_dvd h128 h9
      norm_num at hh
      exact hh
    rw [card_map_of_injective E.injective]
    have hl : Nat.card (RegularWreathProduct.coordinateSubgroup (Q := C2) lineParabolicSL) = 1152 := by
      rw [Nat.card_congr (RegularWreathProduct.coordinateSubgroupEquiv lineParabolicSL).toEquiv,
        RegularWreathProduct.card,card_lineParabolicSL]
      norm_num [C2,Nat.card_eq_fintype_card]
    rw [hl]
    exact Nat.le_of_dvd Nat.card_pos h1152

/-- A centerless normal binary linear-three square with a solvable Sylow
overgroup containing a cubic plane has no diagram extensions. If the square
is proper, the ambient group is the full inner wreath product. -/
theorem full_wreath_of_solvable_overgroup
    (N B : Subgroup Q) [N.Normal] (e : N ≃* SL × SL)
    (hc : centralizer (N : Set Q) = ⊥) (hq : IsPGroup 2 (Q ⧸ N))
    (T : Sylow 2 Q) (hgen : N ⊔ (T : Subgroup Q) = ⊤)
    (hTB : (T : Subgroup Q) ≤ B) (hB : Group.IsSolvable B)
    (h9 : 9 ∣ Nat.card B) (hne : N ≠ ⊤) : Nonempty (Q ≃* W SL) := by
  obtain ⟨E,_⟩ := full_wreath_marking_of_solvable_overgroup N B e hc hq T hgen hTB hB h9 hne
  exact ⟨E⟩

end Matrix.PSL3Two.SquareParabolic
