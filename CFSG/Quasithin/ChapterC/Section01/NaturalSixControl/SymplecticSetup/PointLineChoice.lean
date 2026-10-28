module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ShiftedSeedChoice
/-!
# A moving-line conjugate with the same generating edge

Choose a neighboring kernel that generates the vertex stabilizer together
with the opposite critical layer. Natural-module transitivity sends the
nonzero vector of the prescribed moving line onto that neighbor's fixed
moving line. The same conjugator therefore retains both the edge witness
and the earlier generating-centralizer property. If the resulting line
centralized the opposite layer, its nonzero vector would centralize the
whole vertex group, contradicting the natural moving layer's zero center.

Conjugation transports the construction to any critical starting vertex.
The literal SourceData application preserves its characteristic replacement.

Source: MS93 (5.9), the second starred choice, printed pp.920--921.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

private theorem exists_moving_line_edge_generator_base (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    {e : Vertex R} (p : CriticalPath R s.geometry (alpha R) e)
    (H : Subgroup (FreeAmalgam R)) (hHU : H≤U R (alpha R))
    (hH : H≠⊥) (hcard : Nat.card H≤2) :
    ∃ t : Vertex R, Adjacent R (alpha R) t ∧ Q R t⊔Z R e=stabilizer R (alpha R) ∧
      ∃ y∈Ltilde R (alpha R),
        H.map (MulAut.conj y).toMonoidHom=U R (alpha R)⊓Z R t ∧
        (stabilizer R (alpha R)⊓centralizer (H.map (MulAut.conj y).toMonoidHom:Set (FreeAmalgam R)))⊔
          Z R e=stabilizer R (alpha R) ∧
        ¬H.map (MulAut.conj y).toMonoidHom≤centralizer (Z R e:Set (FreeAmalgam R)) := by
  have hp : R.map s.projection=Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
      (MulAut.conj u).toMonoidHom := by simpa only [Model.pointCore_eq_exceptional] using hfull
  obtain ⟨t,hat,hgen⟩ := s.exists_generating_neighbor h u hp p
  let J := U R (alpha R)⊓Z R t
  have hJ : Nat.card J=2 := s.moving_inf_edge_card h u hfull rfl hat
  have hJne : J≠⊥ := by intro he; rw [he,card_bot] at hJ; omega
  let : Nontrivial J := (nontrivial_iff_ne_bot J).mpr hJne
  let := finite_Z R (alpha R)
  let : Finite J := Finite.of_injective (inclusion (inf_le_left.trans (U_le_Z _))) (inclusion_injective _)
  let : Finite H := Finite.of_injective (inclusion (hHU.trans (U_le_Z _))) (inclusion_injective _)
  let : Nontrivial H := (nontrivial_iff_ne_bot H).mpr hH
  have hc : Nat.card H=2 := by have hh := Finite.one_lt_card (α:=H); omega
  obtain ⟨z,hzn,hunique⟩ := (Nat.card_eq_two_iff' (1:H)).mp hc
  obtain ⟨v,hvn⟩ := exists_ne (1:J)
  have hzn' : (z:FreeAmalgam R)≠1 := fun he => hzn (Subtype.ext he)
  have hvn' : (v:FreeAmalgam R)≠1 := fun he => hvn (Subtype.ext he)
  obtain ⟨y,hy,hyz⟩ := s.moving_nonzero_conjugate h (hHU z.property) v.property.1 hzn' hvn'
  have hmap : H.map (MulAut.conj y).toMonoidHom=J := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      by_cases hx1 : x=1
      · simpa only [hx1,map_one] using J.one_mem
      · have he : (⟨x,hx⟩:H)=z := hunique _ (fun hh => hx1 (congrArg Subtype.val hh))
        change y*x*y⁻¹∈J
        have hex : x=(z:FreeAmalgam R) := congrArg Subtype.val he
        rw [hex,hyz]
        exact v.property
    · rw [card_map_of_injective (MulAut.conj y).injective,hJ,hc]
  have htG : Q R t≤stabilizer R (alpha R) := fun _ hx => hx.2 _ (adjacent_symm R hat)
  have htcol : color R t≠false := Ne.symm (adjacent_color_ne R hat)
  have hJC : J≤centralizer (Q R t:Set (FreeAmalgam R)) := by
    intro x hx
    have hz := hx.2
    rw [Z,if_neg htcol] at hz
    exact (mem_omegaCenter_iff.mp hz).2.2
  have hqt : Q R t≤centralizer (H.map (MulAut.conj y).toMonoidHom:Set (FreeAmalgam R)) := by
    rw [hmap]
    exact le_centralizer_iff.mp hJC
  refine ⟨t,hat,hgen,y,hy,hmap,?_,?_⟩
  · apply le_antisymm (sup_le inf_le_left
      (critical_Z_le_stabilizer R s.geometry (alpha R) rfl s.criticalDistance_pos p.critical))
    conv_lhs => rw [←hgen]
    exact sup_le_sup_right (le_inf htG hqt) _
  · intro hh
    have hvC : (v:FreeAmalgam R)∈centralizer (stabilizer R (alpha R):Set (FreeAmalgam R)) := by
      have hG : stabilizer R (alpha R)≤centralizer (J:Set (FreeAmalgam R)) := by
        rw [←hgen]
        exact sup_le (le_centralizer_iff.mp hJC) (le_centralizer_iff.mp (hmap ▸ hh))
      exact (le_centralizer_iff.mp hG) v.property
    have hvG : (v:FreeAmalgam R)∈stabilizer R (alpha R) :=
      (Z_le_stabilizer R _) ((U_le_Z _) v.property.1)
    have hvc : (v:FreeAmalgam R)∈(center (stabilizer R (alpha R))).map
        (stabilizer R (alpha R)).subtype := by
      refine ⟨⟨v,hvG⟩,?_,rfl⟩
      apply mem_center_iff.mpr
      intro x
      exact Subtype.ext (hvC x.val x.property)
    have hvbot : (v:FreeAmalgam R)∈(⊥:Subgroup (FreeAmalgam R)) := by
      rw [←s.movingLayer_inf_stabilizer_center_eq_bot h]
      exact ⟨v.property.1,hvc⟩
    exact hvn' (mem_bot.mp hvbot)
/-- One conjugator gives the noncentral moving line and its generating edge. -/
theorem exists_moving_line_edge_generator_at (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    {c d : Vertex R} (hc : color R c=false)
    (hcrit : CriticalPair R c d (s.geometry.exists_critical c hc))
    (H : Subgroup (FreeAmalgam R)) (hHU : H ≤ U R c)
    (hH : H ≠ ⊥) (hcard : Nat.card H ≤ 2) :
    ∃ t : Vertex R, Adjacent R c t ∧ Q R t⊔Z R d=stabilizer R c ∧
      ∃ y ∈ stabilizer R c,
      H.map (MulAut.conj y).toMonoidHom=U R c⊓Z R t ∧
      (stabilizer R c ⊓ centralizer (H.map (MulAut.conj y).toMonoidHom : Set (FreeAmalgam R))) ⊔
        Z R d = stabilizer R c ∧
      ¬ H.map (MulAut.conj y).toMonoidHom ≤ centralizer (Z R d : Set (FreeAmalgam R)) := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color R hc
  have hbase : act R g⁻¹ (mVertex R g)=alpha R := by
    simp only [act_mVertex,mul_inv_cancel]; rfl
  have hbasecol : color R (act R g⁻¹ (mVertex R g))=false := by rw [hbase]; rfl
  have hcrit' := (criticalPair_act_iff R g⁻¹ (mVertex R g) d
    (s.geometry.exists_critical _ hc) (s.geometry.exists_critical _ hbasecol)).mpr hcrit
  have hcrit0 : CriticalPair R (alpha R) (act R g⁻¹ d) (s.geometry.exists_critical _ rfl) := by
    simpa only [hbase] using hcrit'
  let H0 := H.map (MulAut.conj g).toMonoidHom
  have hU : (U R (mVertex R g)).map (MulAut.conj g).toMonoidHom = U R (alpha R) := by
    have he := U_act R g⁻¹ (mVertex R g)
    simpa only [inv_inv,hbase] using he.symm
  have hH0 : H0 ≠ ⊥ := by
    intro hz
    apply hH
    apply map_injective (f:=(MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    simpa only [H0,Subgroup.map_bot] using hz
  have hc0 : Nat.card H0 ≤ 2 := by
    dsimp only [H0]
    rw [card_map_of_injective (MulAut.conj g).injective]
    exact hcard
  obtain ⟨t0,ht0,hkernel0,y0,hy0,hline0,hgen0,hmove0⟩ := s.exists_moving_line_edge_generator_base h u hfull
    (CriticalPath.ofPair rfl hcrit0) H0 ((map_mono hHU).trans_eq hU) hH0 hc0
  let y := g⁻¹*y0*g
  let f := (MulAut.conj g⁻¹).toMonoidHom
  have hG : (stabilizer R (alpha R)).map f=stabilizer R (mVertex R g) := by
    simpa only [alpha,act_mVertex,one_mul] using (stabilizer_act R g (alpha R)).symm
  have hZ : (Z R (act R g⁻¹ d)).map f=Z R d := by
    rw [←Z_act,←act_mul,inv_mul_cancel,act_one]
  have hHmap : (H0.map (MulAut.conj y0).toMonoidHom).map f = H.map (MulAut.conj y).toMonoidHom := by
    dsimp only [H0]
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change g⁻¹*(y0*(g*x*g⁻¹)*y0⁻¹)*(g⁻¹)⁻¹=(g⁻¹*y0*g)*x*(g⁻¹*y0*g)⁻¹
    group
  have hy : y ∈ stabilizer R (mVertex R g) := by
    rw [←hG]
    have he : f y0=y := by
      change g⁻¹*y0*(g⁻¹)⁻¹=g⁻¹*y0*g
      rw [inv_inv]
    rw [←he]
    exact mem_map_of_mem f (Ltilde_le_stabilizer _ hy0)
  have hact : act R g (alpha R)=mVertex R g := by
    simp only [alpha,act_mVertex,one_mul]
  have hQt : (Q R t0).map f=Q R (act R g t0) := (Q_act R g t0).symm
  have hZt : (Z R t0).map f=Z R (act R g t0) := (Z_act R g t0).symm
  have hUb : (U R (alpha R)).map f=U R (mVertex R g) := by
    rw [←U_act,hact]
  refine ⟨act R g t0,?_,?_,y,hy,?_,?_,?_⟩
  · rw [←hact]
    exact (adjacent_act_iff R g _ _).mpr ht0
  · have hh := congrArg (Subgroup.map f) hkernel0
    rwa [Subgroup.map_sup,hQt,hZ,hG] at hh
  · have hh := congrArg (Subgroup.map f) hline0
    rwa [hHmap,Subgroup.map_inf _ _ f (MulAut.conj g⁻¹).injective,hUb,hZt] at hh
  · have hh := congrArg (Subgroup.map f) hgen0
    rw [Subgroup.map_sup,←map_inf_centralizer_of_injective f (MulAut.conj g⁻¹).injective,
      hG,hZ,hHmap] at hh
    exact hh
  · intro hh
    apply hmove0
    intro x hx z hz
    have hfx : f x ∈ H.map (MulAut.conj y).toMonoidHom := hHmap ▸ mem_map_of_mem f hx
    have hfz : f z ∈ Z R d := hZ ▸ mem_map_of_mem f hz
    apply (show Function.Injective f from (MulAut.conj g⁻¹).injective)
    simpa only [map_mul] using hh hfx (f z) hfz


end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K] {L W : Subgroup K} [L.Normal] [W.Normal]
  {T : Sylow 2 K} (d : NaturalSixControl.SourceData L W T)

/-- The actual reduction supplies one line conjugator together with the
same generating edge, or returns the alternating-block alternative. -/
theorem reducedSource_block_or_moving_line_edge_generator (hm : IntrinsicMSPair d)
    (r : CharacteristicReduction (L.subgroupOf (L⊔d.B)) (d.B.subgroupOf (L⊔d.B)))
    {c f : Vertex r.radical} (hc : color r.radical c=false)
    (hcrit : CriticalPair r.radical c f (((originalSource d hm).reduce r).geometry.exists_critical c hc))
    (H : Subgroup (FreeAmalgam r.radical)) (hHU : H≤U r.radical c)
    (hH : H≠⊥) (hcard : Nat.card H≤2) :
    IsAlternatingBlock L 6 ∨
      ∃ t : Vertex r.radical, Adjacent r.radical c t ∧
        Q r.radical t⊔Z r.radical f=stabilizer r.radical c ∧
        ∃ y∈stabilizer r.radical c,
          H.map (MulAut.conj y).toMonoidHom=U r.radical c⊓Z r.radical t ∧
          (stabilizer r.radical c⊓centralizer
            (H.map (MulAut.conj y).toMonoidHom:Set (FreeAmalgam r.radical)))⊔Z r.radical f=
              stabilizer r.radical c ∧
          ¬H.map (MulAut.conj y).toMonoidHom≤centralizer (Z r.radical f:Set (FreeAmalgam r.radical)) := by
  rcases reducedSource_block_or_full_point_image d hm r with hb|hf
  · exact Or.inl hb
  · exact Or.inr (Source.exists_moving_line_edge_generator_at ((originalSource d hm).reduce r)
      (reduced_nativeCentralLayer d hm r) d.relabeler.val⁻¹
      (by simpa only [Model.pointCore_eq_exceptional] using hf) hc hcrit H hHU hH hcard)
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
