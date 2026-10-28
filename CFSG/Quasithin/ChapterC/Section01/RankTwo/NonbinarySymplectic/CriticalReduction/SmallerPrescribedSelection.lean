module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SmallerSelectionPosition
public import Theory.SpecificGroups.SymplecticFour.PrescribedActorPlaneGeneration
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SmallerSelection
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SmallerSelectionPosition

/-!
# Both prescribed endpoints generate with the same smaller-mover selectors

Two critical paths with the same first edge put their whole endpoint actors
inside the original parabolic preimage, by actual endpoint absorption. Their
distinct fixed kernels on the whole Z-layer imply distinct quotient images.
The positioned selector retains its original witnesses and both plane images;
the large prescribed-actor theorem then gives generation with the two unchanged
full endpoints for each member of that same selected pair.

Source: MS93 (5.6)(a), printed p.917, used with (5.12)(3), printed p.927.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit

private theorem prescribed_map_conj_mul {G : Type*} [Group G]
    (A : Subgroup G) (g k : G) :
    (A.map (MulAut.conj k).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g*k)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply,mul_assoc]

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The same two positioned selectors generate with both unchanged full
critical endpoints. Every original selector and plane-coordinate clause remains. -/
theorem Input.replacement_smaller_prescribed_root_selection
    {geometry : Geometry d.radical} {a z₁ z₂ t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z₁)
    (companion : CriticalPath d.radical geometry a z₂)
    (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t)
    (hfirst : path.walk.getVert 1=t) (hcfirst : companion.walk.getVert 1=t)
    (hsmall₁ : (Q d.radical a).relIndex (Z d.radical z₁) < Nat.card F^2)
    (hsmall₂ : (Q d.radical a).relIndex (Z d.radical z₂) < Nat.card F^2)
    (B : BinaryField) (hB : B.degree=n)
    (f : stabilizer d.radical a →* Sp B.Carrier) (hf : Function.Surjective f)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype=Q d.radical a)
    (hTf : ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent)
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f))
    (hJplane : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a) ≤
        ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f)
    (hJlarge : Nat.card F^2 < (Q d.radical a).relIndex
      (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2)))
    (hne : Z d.radical a ⊓ centralizer (Z d.radical z₁ : Set (FreeAmalgam d.radical)) ≠
      Z d.radical a ⊓ centralizer (Z d.radical z₂ : Set (FreeAmalgam d.radical))) :
    let D := (((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f).map
      (stabilizer d.radical a).subtype
    let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)
    ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
      (J.map (MulAut.conj g).toMonoidHom ⊔ Z d.radical z₁) ⊔
        (Z d.radical z₁).map (MulAut.conj x).toMonoidHom = stabilizer d.radical a ∧
      (D.map (MulAut.conj g).toMonoidHom ⊔
        (D.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = stabilizer d.radical a) ∧
      ((Z d.radical a ⊓ centralizer (J.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical))) ⊓
        centralizer ((J.map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj x⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) =
          Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
      x ∈ normalizer (D : Set (FreeAmalgam d.radical)) ∧
      x ∈ (planeParabolic.comap f).map (stabilizer d.radical a).subtype ∧
      ((J.map (MulAut.conj g).toMonoidHom ⊔ Z d.radical z₁) ⊔ Z d.radical z₂ =
        stabilizer d.radical a) ∧
      (((J.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom ⊔
          Z d.radical z₁) ⊔ Z d.radical z₂ = stabilizer d.radical a) ∧
      ∃ c : Sp B.Carrier,
        (((D.subgroupOf (stabilizer d.radical a)).map f).map
          (MulAut.conj c).toMonoidHom =
          ((CentralRootGeometry.wing true).map (unipotent (F := B.Carrier)).subtype).map
            (MulAut.conj (TwoConjugate.opposition (F := B.Carrier))).toMonoidHom) ∧
        ((((D.map (MulAut.conj g).toMonoidHom).subgroupOf (stabilizer d.radical a)).map f).map
          (MulAut.conj c).toMonoidHom =
          (CentralRootGeometry.wing true).map (unipotent (F := B.Carrier)).subtype) ∧
        ((((Z d.radical z₁).subgroupOf (stabilizer d.radical a)).map f).map
          (MulAut.conj c).toMonoidHom = RootSubgroup.group 1) ∧
        (((((Z d.radical z₁).map (MulAut.conj x).toMonoidHom).subgroupOf
          (stabilizer d.radical a)).map f).map
          (MulAut.conj c).toMonoidHom = RootSubgroup.group 3) := by
  dsimp only
  let S := stabilizer d.radical a
  let P := (CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype
  let D₀ := P.comap f
  let D := D₀.map S.subtype
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  let J₀ := J.subgroupOf S
  let E₁ := (Z d.radical z₁).subgroupOf S
  let E₂ := (Z d.radical z₂).subgroupOf S
  let := finite_stabilizer d.radical a
  have hDS : D ≤ S := (map_le_range _ _).trans_eq (range_subtype _)
  have hJS : J ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans
    (fun _ hx => hx.2 a (adjacent_symm d.radical hat))
  have hDsub : D.subgroupOf S=D₀ := comap_map_eq_self_of_injective S.subtype_injective _
  have hJ₀D : J₀ ≤ D₀ := hJplane
  have hz₁J := h.replacement_root_endpoint_le_small_mover d path hb hat hfirst hsmall₁
    B hB f hf hTf hindex hJplane
  have hz₂J := h.replacement_root_endpoint_le_small_mover d companion hb hat hcfirst hsmall₂
    B hB f hf hTf hindex hJplane
  have hz₁S : Z d.radical z₁ ≤ S := hz₁J.trans hJS
  have hz₂S : Z d.radical z₂ ≤ S := hz₂J.trans hJS
  have hE₁D : E₁.map f ≤ D₀.map f := map_mono ((comap_mono hz₁J).trans hJ₀D)
  have hE₂D : E₂.map f ≤ D₀.map f := map_mono ((comap_mono hz₂J).trans hJ₀D)
  obtain ⟨hc₁,hd₁⟩ := h.replacement_small_critical_image_dimensions d path hb hsmall₁ B hB f hfQ hindex
  obtain ⟨hc₂,hd₂⟩ := h.replacement_small_critical_image_dimensions d companion hb hsmall₂ B hB f hfQ hindex
  have hEne : E₁.map f ≠ E₂.map f := by
    intro he
    have hp := congrArg (fun A : Subgroup (Sp B.Carrier) => A.comap f) he
    rw [comap_map_eq,comap_map_eq] at hp
    have hamb := congrArg (fun A : Subgroup S => A.map S.subtype) hp
    rw [Subgroup.map_sup,Subgroup.map_sup,map_subgroupOf_eq_of_le hz₁S,
      map_subgroupOf_eq_of_le hz₂S,hfQ] at hamb
    have hsup : Q d.radical a ⊔ Z d.radical z₁=Q d.radical a ⊔ Z d.radical z₂ := by
      simpa only [sup_comm] using hamb
    have hZQ := commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a path.start_color)
    apply hne
    rw [←Subgroup.SmallMover.fixed_inf_sup (Z d.radical a) (Q d.radical a) (Z d.radical z₁) hZQ,
      ←Subgroup.SmallMover.fixed_inf_sup (Z d.radical a) (Q d.radical a) (Z d.radical z₂) hZQ,hsup]
  have hcard : Nat.card B.Carrier=Nat.card F := by rw [B.card_eq,hB,h.field_card]
  have hq : 2 < Nat.card B.Carrier := by
    rw [B.card_eq,hB]
    exact lt_of_lt_of_le (by decide : 2<2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hJc : Nat.card B.Carrier^2 < Nat.card (J₀.map f) := by
    rw [←relIndex_ker]
    have hh := relIndex_map_map_of_injective f.ker J₀ S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le hJS] at hh
    rw [←hh,hcard]
    exact hJlarge
  have hsat := h.replacement_small_mover_parabolic_intersection d geometry hb path.start_color hat
    B hB f hf hindex hJplane
  change Q d.radical t ⊓ D=J at hsat
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) path.start_color hat
  have hQT : Q d.radical a ≤ Q d.radical t := by
    rw [←hjQ,←hjR]
    exact map_mono (h.replacement_core_le d)
  have hkD : f.ker ≤ D₀ := by
    intro y hy
    change f y ∈ P
    rw [MonoidHom.mem_ker.mp hy]
    exact P.one_mem
  have hkJ : f.ker ≤ J₀ := by
    intro y hy
    have hyQ : y.val ∈ Q d.radical a := hfQ ▸ mem_map_of_mem S.subtype hy
    change y.val ∈ J
    rw [←hsat]
    exact ⟨hQT hyQ,mem_map_of_mem S.subtype (hkD hy)⟩
  obtain ⟨g,hg,x,hx,hgen,hpair,hfixed,hxn,hxp,c,hDc,hDgc,hEc,hExc⟩ :=
    h.replacement_smaller_mover_root_selection_positioned d path hb hat hfirst hsmall₁
      B hB f hf hfQ hTf hindex hJplane
  let gs : S := ⟨g,Ltilde_le_stabilizer a hg⟩
  let xs : S := ⟨x,Ltilde_le_stabilizer a hx⟩
  let J₁ := J₀.map (MulAut.conj gs).toMonoidHom
  let J₂ := J₁.map (MulAut.conj xs⁻¹).toMonoidHom
  have hDc₀ : (D₀.map f).map (MulAut.conj c).toMonoidHom =
      P.map (MulAut.conj (TwoConjugate.opposition (F := B.Carrier))).toMonoidHom := by
    have hh := hDc
    change ((D.subgroupOf S).map f).map (MulAut.conj c).toMonoidHom = _ at hh
    rwa [hDsub] at hh
  have hDgc₀ : ((D₀.map (MulAut.conj gs).toMonoidHom).map f).map
      (MulAut.conj c).toMonoidHom=P := by
    have hh := hDgc
    rw [subgroupOf_conjugate_eq D hDS gs,hDsub] at hh
    exact hh
  have hJ₁P : (J₁.map f).map (MulAut.conj c).toMonoidHom ≤ P :=
    hDgc₀ ▸ map_mono (map_mono (map_mono hJ₀D))
  have hJ₁c : Nat.card B.Carrier^2 < Nat.card (J₁.map f) := by
    change Nat.card B.Carrier^2 < Nat.card ((J₀.map (MulAut.conj gs).toMonoidHom).map f)
    rw [Subgroup.image_conjugate,card_map_of_injective (MulAut.conj (f gs)).injective]
    exact hJc
  have hJ₂c : Nat.card B.Carrier^2 < Nat.card (J₂.map f) := by
    change Nat.card B.Carrier^2 < Nat.card ((J₁.map (MulAut.conj xs⁻¹).toMonoidHom).map f)
    rw [Subgroup.image_conjugate,card_map_of_injective (MulAut.conj (f xs⁻¹)).injective]
    exact hJ₁c
  have hDnormal : D₀.map (MulAut.conj xs).toMonoidHom=D₀ := by
    apply Subgroup.map_injective S.subtype_injective
    rw [Subgroup.image_conjugate]
    exact mem_normalizer_iff_map_conj_eq.mp hxn
  have hPnormal : (D₀.map f).map (MulAut.conj (f xs)).toMonoidHom=D₀.map f := by
    rw [←Subgroup.image_conjugate,hDnormal]
  have hDcx : (D₀.map f).map (MulAut.conj (c*f xs)).toMonoidHom=
      P.map (MulAut.conj (TwoConjugate.opposition (F := B.Carrier))).toMonoidHom := by
    rw [←prescribed_map_conj_mul,hPnormal]
    exact hDc₀
  have hJ₂P : (J₂.map f).map (MulAut.conj (c*f xs)).toMonoidHom ≤ P := by
    change ((J₁.map (MulAut.conj xs⁻¹).toMonoidHom).map f).map
      (MulAut.conj (c*f xs)).toMonoidHom ≤ P
    rw [Subgroup.image_conjugate,map_inv,prescribed_map_conj_mul,
      show (c*f xs)*(f xs)⁻¹=c by group]
    exact hJ₁P
  have hmodel₁ := PrescribedActorPlaneGeneration.positioned_large_actor_and_prescribed_full_roots_generate
    hq (D₀.map f) (J₁.map f) (E₁.map f) (E₂.map f) c hDc₀ hJ₁P hJ₁c
    hE₁D hE₂D hc₁ hc₂ hd₁ hd₂ hEne
  have hmodel₂ := PrescribedActorPlaneGeneration.positioned_large_actor_and_prescribed_full_roots_generate
    hq (D₀.map f) (J₂.map f) (E₁.map f) (E₂.map f) (c*f xs) hDcx hJ₂P hJ₂c
    hE₁D hE₂D hc₁ hc₂ hd₁ hd₂ hEne
  have hkJ₁ : f.ker ≤ J₁ := kernel_le_conjugate f J₀ hkJ gs
  have hkJ₂ : f.ker ≤ J₂ := kernel_le_conjugate f J₁ hkJ₁ xs⁻¹
  have hfull₁ : (J₁ ⊔ E₁) ⊔ E₂=⊤ := by
    apply full_of_full_image f _ (hkJ₁.trans (le_sup_left.trans le_sup_left))
    simpa only [Subgroup.map_sup] using hmodel₁
  have hfull₂ : (J₂ ⊔ E₁) ⊔ E₂=⊤ := by
    apply full_of_full_image f _ (hkJ₂.trans (le_sup_left.trans le_sup_left))
    simpa only [Subgroup.map_sup] using hmodel₂
  have hprescribed₁ := congrArg (Subgroup.map S.subtype) hfull₁
  change ((J₀.map (MulAut.conj gs).toMonoidHom ⊔ E₁) ⊔ E₂).map S.subtype=_ at hprescribed₁
  rw [Subgroup.map_sup,Subgroup.map_sup,Subgroup.image_conjugate,
    map_subgroupOf_eq_of_le hJS,map_subgroupOf_eq_of_le hz₁S,map_subgroupOf_eq_of_le hz₂S,
    ←MonoidHom.range_eq_map,range_subtype] at hprescribed₁
  have hprescribed₂ := congrArg (Subgroup.map S.subtype) hfull₂
  change (((J₀.map (MulAut.conj gs).toMonoidHom).map (MulAut.conj xs⁻¹).toMonoidHom ⊔ E₁) ⊔ E₂).map
    S.subtype=_ at hprescribed₂
  rw [Subgroup.map_sup,Subgroup.map_sup,Subgroup.image_conjugate,Subgroup.image_conjugate,
    map_subgroupOf_eq_of_le hJS,map_subgroupOf_eq_of_le hz₁S,map_subgroupOf_eq_of_le hz₂S,
    ←MonoidHom.range_eq_map,range_subtype] at hprescribed₂
  exact ⟨g,hg,x,hx,hgen,hpair,hfixed,hxn,hxp,hprescribed₁,hprescribed₂,c,hDc,hDgc,hEc,hExc⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
