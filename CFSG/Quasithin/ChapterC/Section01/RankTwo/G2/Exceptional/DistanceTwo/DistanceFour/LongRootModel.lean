module
public import Theory.Representation.G2NaturalOffenders
public import Theory.AtlasPort.LinearGroups.G2.BinarySecondParabolic
public import Theory.AtlasPort.LinearGroups.G2.LieSylowCenter

/-!
Adapted from the checked Chapter15 MarkedMS.G2Reconstruction proof to the
exceptional MS2(b) input. Only the two-group and core-containment consequences
of MS2 are used; the original SmallMSPair interface is unchanged.

# Simultaneous root coordinates for the G₂ critical-edge calculation

First align the offender with the A–B–C subgroup. Sylow conjugacy inside
its normalizer then puts the normalizing two-group inside the standard
unipotent group while preserving that offender. On the full trace-zero
preimage of its fixed three-space, every unipotent displacement is a
highest-long-root displacement. The natural quotient calculation is
transported by that same conjugating element.

These are the model calculations for the last paragraph of MS93 (3.8),
printed p.879. `LongRootAuxiliary` retains the original actor and critical
pair when using the alignment. Root formulas use the existing ATLAS port;
see LICENSES/ATLAS.txt. No abstract matrix replacement is introduced.
-/

open Subgroup Representation Representation.BinaryOffender
open Atlas.G2
public noncomputable section
namespace CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction.DistanceTwo.DistanceFour.LongRootModel

private theorem elementary_eq : (EvenTwoRank.elementary (ZMod 2)) = BinaryCore.elementary := by
  apply le_antisymm
  · rintro x ⟨v,rfl⟩
    refine ⟨⟨v.toAdd 0,v.toAdd 1,v.toAdd 2,0,0⟩,⟨rfl,rfl⟩,rfl⟩
  · rintro x ⟨v,hv,rfl⟩
    refine ⟨Multiplicative.ofAdd ![v.a,v.b,v.c],?_⟩
    change unipotentProduct ![v.a,v.b,v.c,0,0,0] =
      unipotentProduct ![v.a,v.b,v.c,v.d,v.e,0]
    rw [hv.1,hv.2]

private theorem unipotent_normalizes : unipotent (K := ZMod 2) ≤ normalizer ((EvenTwoRank.elementary (ZMod 2)) : Set (Model (ZMod 2))) := by
  rw [elementary_eq]
  exact BinaryCore.unipotent_normalizes_elementary

private theorem align_in_normalizer (B : Subgroup (Model (ZMod 2))) (hB : IsPGroup 2 B)
    (hn : B ≤ normalizer ((EvenTwoRank.elementary (ZMod 2)) : Set (Model (ZMod 2)))) :
    ∃ n : normalizer ((EvenTwoRank.elementary (ZMod 2)) : Set (Model (ZMod 2))),
      B.map (MulAut.conj n.val).toMonoidHom ≤ unipotent := by
  let N := normalizer ((EvenTwoRank.elementary (ZMod 2)) : Set (Model (ZMod 2)))
  obtain ⟨S,hBS⟩ := (hB.comap_subtype (K := N)).exists_le_sylow
  obtain ⟨n,hnS⟩ := MulAction.exists_smul_eq N S
    ((LieParabolicSetup.sylow (F := ZMod 2)).subtype unipotent_normalizes)
  refine ⟨n,?_⟩
  rintro _ ⟨x,hx,rfl⟩
  have hh : MulAut.conj n ⟨x,hn hx⟩ ∈
      ((LieParabolicSetup.sylow (F := ZMod 2)).subtype unipotent_normalizes : Subgroup N) := by
    rw [←hnS]
    exact mem_map_of_mem (MulAut.conj n).toMonoidHom (hBS hx)
  exact hh

theorem simultaneous_alignment (E B : Subgroup (Model (ZMod 2)))
    (hE : IsOffender (Restricted.NaturalCoordinates.action (ZMod 2)) E)
    (hB : IsPGroup 2 B) (hn : B ≤ normalizer (E : Set (Model (ZMod 2)))) :
    ∃ g : (Model (ZMod 2)), E = (EvenTwoRank.elementary (ZMod 2)).map (MulAut.conj g).toMonoidHom ∧
      B ≤ unipotent.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨k,hk⟩ := NaturalOffenders.offender_conjugate_elementary
    (F := ZMod 2) (n := 1) (by norm_num) (by decide) E hE
  let f := MulAut.conj k⁻¹
  have hEback : E.map f.toMonoidHom = (EvenTwoRank.elementary (ZMod 2)) := by
    rw [hk,map_map]
    have he : f.toMonoidHom.comp (MulAut.conj k).toMonoidHom = MonoidHom.id (Model (ZMod 2)) := by
      ext x
      simp [f,MulAut.conj_apply,mul_assoc]
    rw [he,map_id]
  have hn' : B.map f.toMonoidHom ≤ normalizer ((EvenTwoRank.elementary (ZMod 2)) : Set (Model (ZMod 2))) := by
    rw [←hEback]
    exact (map_mono hn).trans (le_normalizer_map f.toMonoidHom)
  obtain ⟨n,hn⟩ := align_in_normalizer (B.map f.toMonoidHom) (hB.map _) hn'
  refine ⟨k*n.val⁻¹,?_,?_⟩
  · have he := mem_normalizer_iff_map_conj_eq.mp
      ((normalizer ((EvenTwoRank.elementary (ZMod 2)) : Set (Model (ZMod 2)))).inv_mem n.property)
    calc
      E = (EvenTwoRank.elementary (ZMod 2)).map (MulAut.conj k).toMonoidHom := hk
      _ = ((EvenTwoRank.elementary (ZMod 2)).map (MulAut.conj n.val⁻¹).toMonoidHom).map
          (MulAut.conj k).toMonoidHom := congrArg (fun A => A.map (MulAut.conj k).toMonoidHom) he.symm
      _ = _ := by
        rw [map_map]
        congr 1
  · intro x hx
    have hx' := hn (mem_map_of_mem (MulAut.conj n.val).toMonoidHom
      (mem_map_of_mem f.toMonoidHom hx))
    refine ⟨_,hx',?_⟩
    simp [f,MulAut.conj_apply,mul_assoc]

open Atlas.SplitOctonion Atlas.G2.Explicit
theorem unipotent_displacement_upper (t : Fin 6 → ZMod 2)
    (x : Natural.TraceZero (ZMod 2))
    (hx : Restricted.NaturalCoordinates.projection (ZMod 2) x ∈ NaturalOffenders.upper) :
    ∃ y : Natural.TraceZero (ZMod 2),
      Natural.traceZeroAction (ZMod 2) (unipotentProduct t) x - x =
        Natural.traceZeroAction (ZMod 2) (rootA 1) y - y := by
  have h5 : x.val 5 = 0 := hx.1
  have h6 : x.val 6 = 0 := hx.2.1
  have h7 : x.val 7 = 0 := hx.2.2
  have h34 : x.val 4 = x.val 3 := by
    have hh : x.val 3 + x.val 4 = 0 := x.property
    simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right hh
  refine ⟨⟨![0,0,0,0,0,0,t 5*x.val 1+t 3*x.val 2,t 4*x.val 2],by simp [trace]⟩,?_⟩
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp [Natural.traceZeroAction_val,unipotentProduct,rootA,rootB,rootC,rootD,rootE,rootF,
      rootAEquiv,rootBEquiv,rootCEquiv,rootDEquiv,rootEEquiv,rootFEquiv,
      rootALinear,rootBLinear,rootCLinear,rootDLinear,rootELinear,rootFLinear,
      rootAApply,rootBApply,rootCApply,rootDApply,rootEApply,rootFApply,
      h5,h6,h7,h34]
  all_goals simp [sub_eq_add_neg,CharTwo.neg_eq,add_assoc,add_comm,
    CharTwo.add_cancel_left]

end CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction.DistanceTwo.DistanceFour.LongRootModel
namespace CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction.DistanceTwo.DistanceFour.LongRootModel
open Subgroup Representation Representation.BinaryOffender Atlas.G2
local notation "ρ" => Restricted.NaturalCoordinates.action (ZMod 2)
private theorem natural_unipotent_displacement (t : Fin 6 → ZMod 2) (v : Fin 6 → ZMod 2)
    (hv : v ∈ NaturalOffenders.upper) :
    ∃ w : Fin 6 → ZMod 2, ρ (unipotentProduct t) v - v = ρ (rootA 1) w - w := by
  refine ⟨![0,0,0,0,t 5*v 1+t 3*v 2,t 4*v 2],?_⟩
  ext i
  fin_cases i <;> simp [unipotentProduct,map_mul,Module.End.mul_apply,
    Restricted.NaturalCoordinates.action_rootA,Restricted.NaturalCoordinates.action_rootB,
    Restricted.NaturalCoordinates.action_rootC,Restricted.NaturalCoordinates.action_rootD,
    Restricted.NaturalCoordinates.action_rootE,Restricted.NaturalCoordinates.action_rootF,
    hv.1,hv.2.1,hv.2.2,sub_eq_add_neg,CharTwo.neg_eq,add_comm,add_left_comm,
    CharTwo.add_self_eq_zero,CharTwo.add_cancel_left]

theorem natural_displacement (E B : Subgroup (Model (ZMod 2)))
    (g : Model (ZMod 2))
    (hE : E = (EvenTwoRank.elementary (ZMod 2)).map (MulAut.conj g).toMonoidHom)
    (hB : B ≤ unipotent.map (MulAut.conj g).toMonoidHom)
    (b : Model (ZMod 2)) (hb : b ∈ B) (v : Fin 6 → ZMod 2)
    (hv : v ∈ fixedSpace ρ E) :
    ∃ w : Fin 6 → ZMod 2, ρ b v-v = ρ (MulAut.conj g (rootA 1)) w-w := by
  let v' := ρ g⁻¹ v
  have hv' : v' ∈ fixedSpace ρ (EvenTwoRank.elementary (ZMod 2)) := by
    intro a
    have ha : MulAut.conj g a.val ∈ E := by
      rw [hE]
      exact mem_map_of_mem (MulAut.conj g).toMonoidHom a.property
    have hh := congrArg (ρ g⁻¹) (hv ⟨_,ha⟩)
    change ρ g⁻¹ (ρ (g*a.val*g⁻¹) v) = v' at hh
    change ρ a.val v' = v'
    simpa only [map_mul,Module.End.mul_apply,Representation.inv_self_apply] using hh
  have hu : v' ∈ NaturalOffenders.upper := by
    change v' ∈ fixedSpace (NaturalOffenders.binaryAction (F := ZMod 2))
      (EvenTwoRank.elementary (ZMod 2)) at hv'
    rwa [NaturalOffenders.fixedSpace_elementary] at hv'
  obtain ⟨b',hb',rfl⟩ := hB hb
  rw [unipotent_eq_range] at hb'
  obtain ⟨t,rfl⟩ := hb'
  obtain ⟨w,hw⟩ := natural_unipotent_displacement t v' hu
  refine ⟨ρ g w,?_⟩
  calc
    ρ (MulAut.conj g (unipotentProduct t)) v-v =
        ρ g (ρ (unipotentProduct t) v'-v') := by
      simp only [v',MulAut.conj_apply,map_mul,Module.End.mul_apply,map_sub,Representation.self_inv_apply]
    _ = ρ g (ρ (rootA 1) w-w) := by rw [hw]
    _ = _ := by
      simp only [MulAut.conj_apply,map_mul,Module.End.mul_apply,map_sub,Representation.inv_self_apply]
end CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction.DistanceTwo.DistanceFour.LongRootModel
