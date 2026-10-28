module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.CentralSeedSplit
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.CriticalGeneration
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalTransport

/-!
# One noncentral seed conjugate with its generating centralizer

Split the original Z-layer into its natural moving factor and a central
factor. An element outside the fixed core has a nonzero moving factor.
The natural A6 action moves that factor onto the fixed line of a neighbor
whose kernel generates the vertex group together with the opposite critical
Z-layer. The same conjugate therefore has a generating local centralizer
and is not centralized by the opposite Z-layer: otherwise its nonzero
moving factor would lie in the vertex center.

The original source-data application discharges the full point-core marking
or returns the alternating block, retaining the actual characteristic
replacement. Source: MS93 (5.9), the starred conjugate choice on printed
pp.920--922, toward Aschbacher--Smith C.1.37 and 13.7.4(1).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M]
variable {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)

/-- Every actual edge meets the natural moving layer in a line. -/
theorem moving_inf_edge_card (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t) :
    Nat.card (U R a ⊓ Z R t : Subgroup (FreeAmalgam R)) = 2 := by
  have hb : Nat.card (U R (alpha R) ⊓ Z R (beta R) : Subgroup (FreeAmalgam R)) = 2 := by
    have hseed : Z R (beta R) = (omegaCenter R).map (embedM R) := by
      rw [Z,if_neg (by exact Bool.noConfusion : color R (beta R) ≠ false),edgeOmega,Q_beta,
        omegaCenter_map _ _ (embedM_injective R)]
    rw [h.U_eq_module,hseed,←Subgroup.map_inf _ _ _ (embedM_injective R),
      card_map_of_injective (embedM_injective R)]
    apply s.module_inf_seed_card u
    simpa only [Model.pointCore_eq_exceptional] using hfull
  obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common R a t).mp hat
  · rcases hg with ⟨rfl,rfl⟩
    have he := card_map_of_injective (K:=U R (alpha R) ⊓ Z R (beta R))
      (f:=(MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective,←U_act,←Z_act] at he
    simp only [alpha,beta,act_mVertex,act_hVertex,one_mul] at he
    exact he.trans hb
  · rw [hg.1] at ha
    cases ha

/-- The actual component conjugates any two nonzero moving vectors. -/
theorem moving_nonzero_conjugate (h : NativeCentralLayer s)
    {a b : FreeAmalgam R} (ha : a ∈ U R (alpha R)) (hb : b ∈ U R (alpha R))
    (han : a ≠ 1) (hbn : b ≠ 1) :
    ∃ g ∈ Ltilde R (alpha R), g*a*g⁻¹=b := by
  rw [h.U_eq_module] at ha hb
  obtain ⟨a,ha,rfl⟩ := ha
  obtain ⟨b,hb,rfl⟩ := hb
  have han' : (⟨a,ha⟩:W) ≠ 1 := by
    intro he
    apply han
    simpa only [Subgroup.coe_one,map_one] using congrArg (embedM R) (congrArg Subtype.val he)
  have hbn' : (⟨b,hb⟩:W) ≠ 1 := by
    intro he
    apply hbn
    simpa only [Subgroup.coe_one,map_one] using congrArg (embedM R) (congrArg Subtype.val he)
  have hca : (s.coordinates ⟨a,ha⟩).toAdd ≠ 0 := by
    intro he
    apply han'
    apply s.coordinates.injective
    exact Multiplicative.toAdd.injective (by simpa only [map_one,toAdd_one] using he)
  have hcb : (s.coordinates ⟨b,hb⟩).toAdd ≠ 0 := by
    intro he
    apply hbn'
    apply s.coordinates.injective
    exact Multiplicative.toAdd.injective (by simpa only [map_one,toAdd_one] using he)
  obtain ⟨k,hk⟩ := Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalTransport.transitive_nonzero
    _ _ hca hcb
  have hkL : k.val ∈ L.map s.projection := by rw [s.component_image]; exact k.property
  obtain ⟨g,hg,hgk⟩ := hkL
  have hh := s.action g ⟨a,ha⟩
  rw [hgk,hk] at hh
  have hab : MulAut.conjNormal g (⟨a,ha⟩:W)=⟨b,hb⟩ :=
    s.coordinates.injective (Multiplicative.toAdd.injective hh)
  refine ⟨embedM R g,?_,?_⟩
  · rw [Ltilde_alpha,s.residual]
    exact mem_map_of_mem _ hg
  · rw [←map_inv,←map_mul,←map_mul]
    exact congrArg (embedM R) (congrArg Subtype.val hab)

/-- The same component conjugator gives generation and noncentral movement. -/
theorem exists_noncentral_seed_generator (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    {e : Vertex R} (p : DistanceEight.PathCentrality.CriticalPath R s.geometry (alpha R) e)
    {z : FreeAmalgam R} (hz : z ∈ Z R (alpha R)) (hzn : z ∉ fixedCore R (alpha R)) :
    ∃ g ∈ Ltilde R (alpha R),
      (stabilizer R (alpha R) ⊓ centralizer ({g*z*g⁻¹} : Set (FreeAmalgam R))) ⊔ Z R e =
        stabilizer R (alpha R) ∧
      g*z*g⁻¹ ∉ centralizer (Z R e : Set (FreeAmalgam R)) := by
  have hpoint : R.map s.projection =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom := by
    simpa only [Model.pointCore_eq_exceptional] using hfull
  obtain ⟨t,hat,hgen⟩ := s.exists_generating_neighbor h u hpoint p
  obtain ⟨w,hw,d,hd,hwd⟩ := s.exists_moving_central_factors h u hfull hz
  have hdcomm (q : FreeAmalgam R) (hq : q ∈ stabilizer R (alpha R)) : q*d=d*q := by
    obtain ⟨d',hd',hed⟩ := hd.2
    have hh := congrArg Subtype.val (mem_center_iff.mp hd' (⟨q,hq⟩:stabilizer R (alpha R)))
    change q*d'.val=d'.val*q at hh
    change d'.val=d at hed
    simpa only [hed] using hh
  have hwn : w ≠ 1 := by
    intro he
    have hez : z=d := by simpa only [he,one_mul] using hwd.symm
    apply hzn
    rw [hez]
    refine ⟨(s.Z_le_X.trans (omegaCenter_le _)) hd.1,?_⟩
    intro l hl
    exact hdcomm l (Ltilde_le_stabilizer _ hl)
  let H := U R (alpha R) ⊓ Z R t
  have hc : Nat.card H=2 := s.moving_inf_edge_card h u hfull rfl hat
  have hH : H ≠ ⊥ := by intro he; rw [he,card_bot] at hc; omega
  let : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr hH
  obtain ⟨v,hvn⟩ := exists_ne (1:H)
  have hvn' : (v:FreeAmalgam R) ≠ 1 := fun he => hvn (Subtype.ext he)
  obtain ⟨g,hg,hgw⟩ := s.moving_nonzero_conjugate h hw v.property.1 hwn hvn'
  have hgG : g ∈ stabilizer R (alpha R) := Ltilde_le_stabilizer _ hg
  have hzd : g*z*g⁻¹=(v:FreeAmalgam R)*d := by
    rw [←hwd]
    calc
      g*(w*d)*g⁻¹ = (g*w*g⁻¹)*(g*d*g⁻¹) := by group
      _ = (v:FreeAmalgam R)*d := by rw [hgw,hdcomm g hgG,mul_inv_cancel_right]
  have htG : Q R t ≤ stabilizer R (alpha R) := fun _ hq => hq.2 _ (adjacent_symm R hat)
  have htcol : color R t ≠ false := Ne.symm (adjacent_color_ne R hat)
  have hvfix : (v:FreeAmalgam R) ∈ centralizer (Q R t : Set (FreeAmalgam R)) := by
    have hv := v.property.2
    rw [Z,if_neg htcol] at hv
    exact (mem_omegaCenter_iff.mp hv).2.2
  have hqt : Q R t ≤ centralizer ({g*z*g⁻¹}:Set (FreeAmalgam R)) := by
    intro q hq x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    rw [hzd]
    calc
      ((v:FreeAmalgam R)*d)*q = (v:FreeAmalgam R)*(q*d) := by rw [mul_assoc,hdcomm q (htG hq)]
      _ = q*((v:FreeAmalgam R)*d) := by rw [←mul_assoc,←hvfix q hq,mul_assoc]
  have hze : Z R e ≤ stabilizer R (alpha R) :=
    critical_Z_le_stabilizer R s.geometry (alpha R) rfl s.criticalDistance_pos p.critical
  refine ⟨g,hg,?_,?_⟩
  · apply le_antisymm (sup_le inf_le_left hze)
    conv_lhs => rw [←hgen]
    exact sup_le_sup_right (le_inf htG hqt) _
  · intro hzfix
    have hGc : stabilizer R (alpha R) ≤ centralizer ({g*z*g⁻¹}:Set (FreeAmalgam R)) := by
      rw [←hgen]
      apply sup_le hqt
      intro x hx y hy
      obtain rfl := Set.mem_singleton_iff.mp hy
      exact (hzfix x hx).symm
    have hvG : (v:FreeAmalgam R) ∈ stabilizer R (alpha R) :=
      (Z_le_stabilizer R (alpha R)) ((U_le_Z _) v.property.1)
    have hvC : (v:FreeAmalgam R) ∈ (center (stabilizer R (alpha R))).map
        (stabilizer R (alpha R)).subtype := by
      refine ⟨⟨v,hvG⟩,?_,rfl⟩
      apply mem_center_iff.mpr
      intro x
      apply Subtype.ext
      apply mul_right_cancel (b:=d)
      have hh := hGc x.property (g*z*g⁻¹) (Set.mem_singleton _)
      rw [hzd] at hh
      change x.val*(v:FreeAmalgam R)*d=(v:FreeAmalgam R)*x.val*d
      calc
        x.val*(v:FreeAmalgam R)*d = x.val*((v:FreeAmalgam R)*d) := mul_assoc _ _ _
        _ = ((v:FreeAmalgam R)*d)*x.val := hh.symm
        _ = (v:FreeAmalgam R)*x.val*d := by rw [mul_assoc,←hdcomm x.val x.property,←mul_assoc]
    have hvbot : (v:FreeAmalgam R) ∈ (⊥ : Subgroup (FreeAmalgam R)) := by
      rw [←s.movingLayer_inf_stabilizer_center_eq_bot h]
      exact ⟨v.property.1,hvC⟩
    exact hvn' (mem_bot.mp hvbot)

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K]
  {L W : Subgroup K} [L.Normal] [W.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L W T) (h : IntrinsicMSPair d)
local notation "J" => (L ⊔ d.B : Subgroup K)
local notation "R" => d.B.subgroupOf J

/-- The literal characteristic replacement supplies splitting and the starred
noncentral seed choice, with no additional point-core hypothesis. -/
theorem reducedSource_block_or_noncentral_seed_generator
    (r : CharacteristicReduction (L.subgroupOf J) R) {e : Vertex r.radical}
    (p : DistanceEight.PathCentrality.CriticalPath r.radical
      ((originalSource d h).reduce r).geometry (alpha r.radical) e) :
    IsAlternatingBlock L 6 ∨
      (Z r.radical (alpha r.radical) = U r.radical (alpha r.radical) ⊔
        (Z r.radical (alpha r.radical) ⊓
          (center (stabilizer r.radical (alpha r.radical))).map
            (stabilizer r.radical (alpha r.radical)).subtype)) ∧
      ∀ z ∈ Z r.radical (alpha r.radical), z ∉ fixedCore r.radical (alpha r.radical) →
      ∃ g ∈ Ltilde r.radical (alpha r.radical),
        (stabilizer r.radical (alpha r.radical) ⊓
          centralizer ({g*z*g⁻¹}:Set (FreeAmalgam r.radical))) ⊔ Z r.radical e =
            stabilizer r.radical (alpha r.radical) ∧
        g*z*g⁻¹ ∉ centralizer (Z r.radical e : Set (FreeAmalgam r.radical)) := by
  rcases reducedSource_block_or_full_point_image d h r with hb | hf
  · exact Or.inl hb
  · let s := (originalSource d h).reduce r
    have hn := reduced_nativeCentralLayer d h r
    have he : r.radical.map s.projection = Model.E.map
        (MulAut.conj d.relabeler.val⁻¹).toMonoidHom := by
      simpa only [Model.pointCore_eq_exceptional] using hf
    exact Or.inr ⟨s.Z_eq_moving_sup_central hn _ he,
      fun _ hz hzn => s.exists_noncentral_seed_generator hn _ he p hz hzn⟩

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
