module
public import Theory.SpecificGroups.Triality.BinaryTorusNormalizer
public import Theory.GroupAction.PerfectFixedCover
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.InvolutionClasses.ArmsReduction.Weyl
public import Theory.SpecificGroups.Triality.ConcreteBruhat.CartanNormalizer
public import Theory.SpecificGroups.Triality.RadicalCoordinates.ParabolicSplitting

/-!
# Binary triality endpoint normalizer coordinates

Rank-one Bruhat decomposition expresses an endpoint element outside the Borel
with one simple reflection. For an element normalizing the order-seven torus,
coprime fixed-coset lifting chooses its initial unipotent factor in the torus
centralizer. The remaining Borel factor also normalizes the torus, hence has
only the three long-root coordinates and a torus factor.

At the arms endpoint all fixed unipotent elements lie in the normal radical.
The arms reflection therefore preserves their subgroup, and the two long-root
factors combine into one. At the central endpoint its reflection exchanges the
two higher long roots; moving them to the right leaves one binary coordinate
on the left. These exact native words are used for the original
Cartan-aligned reflection pair; no sixth-power equation is assumed or concluded.

Source: the root and Bruhat structure in GLS3 §§2.4,2.6, and the Cartan
comparison in Aschbacher--Smith F.4.15--17, pp.281--283 (`refs/quasithin.pdf`).
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace Triality.Standard.BinaryTorusEndpoints
open Parabolics ConcreteBruhat
open RadicalCoordinates.LeviCommutators
local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "C" => Carrier P

private theorem reflection_normalizes (s : Node) :
    simpleRepresentative P rfl s ∈ normalizer (torus P : Set C) := by
  rw [←weylRepresentative_simple P rfl]
  exact RelativeNormalizer.weylRepresentative_normalizes_torus P rfl _

private theorem rank_one_cells (s : Node) (g : C) (hg : g ∈ parabolic P s) :
    g ∈ borel P ∨ ∃ a ∈ borel P, ∃ b ∈ borel P,
      g = a * simpleRepresentative P rfl s * b := by
  obtain ⟨w,hw,hg⟩ := (FixedDescent.mem_parabolic_iff_exists_cell 1 Nat.zero_lt_one s g).mp hg
  rcases (FoldedCellGeometry.rootRepresentative_mem_parabolicWeyl_iff s w).mp hw with hw | hw
  · left
    rwa [hw,cell_one P rfl] at hg
  · right
    rw [hw] at hg
    obtain ⟨a,ha,b,hb,he⟩ := (mem_cell_iff P rfl _ g).mp hg
    exact ⟨a,ha,b,hb,by simpa only [weylRepresentative_simple P rfl] using he⟩

private theorem fixed_coset_lift (s : Node) (u : C) (hu : u ∈ unipotent P)
    (hf : ∀ t ∈ torus P,
      (simpleRepresentative P rfl s)⁻¹*u⁻¹*t*u*simpleRepresentative P rfl s ∈ borel P) :
    ∃ v ∈ unipotent P ⊓ centralizer (torus P : Set C),
      (simpleRepresentative P rfl s)⁻¹*v⁻¹*u*simpleRepresentative P rfl s ∈ borel P := by
  let w := simpleRepresentative P rfl s
  let Q := torus P
  let U := unipotent P
  let B := borel P
  have hw : w ∈ normalizer (Q : Set C) := reflection_normalizes s
  have hQU : Q ≤ normalizer (U : Set C) :=
    (torus_le_borel P).trans (borel_le_normalizer_unipotent P rfl)
  have hQB : Q ≤ B := torus_le_borel P
  have htw (t : C) (ht : t ∈ Q) : w⁻¹*t*w ∈ B := by
    apply hQB
    simpa only [inv_inv] using (mem_normalizer_iff.mp (inv_mem hw) t).mp ht
  let N : Subgroup C := U ⊓ B.comap (MulAut.conj w⁻¹).toMonoidHom
  have hQN : Q ≤ normalizer (N : Set C) := by
    rw [le_normalizer_iff]
    intro t ht x hx
    refine ⟨(mem_normalizer_iff.mp (hQU ht) x).mp hx.1,?_⟩
    change w⁻¹*(t*x*t⁻¹)*w ∈ B
    have hxB : w⁻¹*x*w ∈ B := hx.2
    convert B.mul_mem (B.mul_mem (htw t ht) hxB) (B.inv_mem (htw t ht)) using 1
    group
  let α : Q →* MulAut C := MulAut.conj.comp Q.subtype
  let act : MulDistribMulAction Q C := MulDistribMulAction.compHom _ α
  let : SMul Q C := act.toSMul
  let : MulDistribMulAction Q C := act
  let : IsInvariant Q C N := ⟨fun t x => by
    change x ∈ N ↔ t.val*x*t.val⁻¹ ∈ N
    exact mem_normalizer_iff.mp (hQN t.property) x⟩
  have hsolv : Group.IsSolvable N := by
    let : Group.IsNilpotent N := ((unipotent_isPGroup_binary P rfl).to_le
      (show N ≤ unipotent P from inf_le_left)).isNilpotent
    infer_instance
  have hcopU : (Nat.card Q).Coprime (Nat.card U) := by
    change (Nat.card (torus P)).Coprime (Nat.card (unipotent P))
    rw [FixedCellCount.card_unipotent, TorusCoordinates.card_torus P rfl]
    decide
  have hcop : (Nat.card Q).Coprime (Nat.card N) :=
    hcopU.of_dvd_right (card_dvd_of_le (show N ≤ U from inf_le_left))
  obtain ⟨n,hn⟩ := Theory.GroupAction.exists_fixed_mul_of_solvable_coprime_displacement
    N hsolv hcop u (fun t => by
      refine ⟨U.mul_mem (U.inv_mem hu) ((mem_normalizer_iff.mp (hQU t.property) u).mp hu),?_⟩
      change w⁻¹*(u⁻¹*(t.val*u*t.val⁻¹))*w ∈ B
      convert B.mul_mem (hf t.val t.property) (htw t.val⁻¹ (inv_mem t.property)) using 1
      dsimp [w]
      group)
  refine ⟨u*n.val,⟨U.mul_mem hu n.property.1,?_⟩,?_⟩
  · intro t ht
    have hh := hn (⟨t,ht⟩ : Q)
    change t*(u*n.val)*t⁻¹=u*n.val at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  · have hh := B.inv_mem n.property.2
    change w⁻¹*(u*n.val)⁻¹*u*w ∈ B
    convert hh using 1
    change _ = (w⁻¹*n.val*w)⁻¹
    group

/-- Exact rank-one factors for a torus normalizer outside the whole Borel. -/
theorem normalizing_endpoint_factors (s : Node) (g : C)
    (hg : g ∈ parabolic P s) (hout : g ∉ borel P)
    (hn : g ∈ normalizer (torus P : Set C)) :
    ∃ v ∈ unipotent P ⊓ centralizer (torus P : Set C),
      ∃ b ∈ borel P ⊓ normalizer (torus P : Set C),
        g = v * simpleRepresentative P rfl s * b := by
  rcases rank_one_cells s g hg with h | ⟨a,ha,b,hb,he⟩
  · exact (hout h).elim
  have hprod : a ∈ (unipotent P : Set C) * torus P := (borel_eq_mul P rfl) ▸ ha
  obtain ⟨u,hu,t,ht,hat⟩ := hprod
  let w := simpleRepresentative P rfl s
  have hw : w ∈ normalizer (torus P : Set C) := reflection_normalizes s
  have htw : w⁻¹*t*w ∈ borel P := by
    apply torus_le_borel P
    simpa only [inv_inv] using (mem_normalizer_iff.mp (inv_mem hw) t).mp ht
  let b' := w⁻¹*t*w*b
  have hb' : b' ∈ borel P := mul_mem htw hb
  have he' : g = u*w*b' := by
    rw [he,←hat]
    dsimp [b',w]
    group
  have hf : ∀ z ∈ torus P, w⁻¹*u⁻¹*z*u*w ∈ borel P := by
    intro z hz
    have hh : g⁻¹*z*g ∈ borel P := torus_le_borel P
      (by simpa only [inv_inv] using (mem_normalizer_iff.mp (inv_mem hn) z).mp hz)
    rw [he'] at hh
    convert (borel P).mul_mem ((borel P).mul_mem hb' hh) (inv_mem hb') using 1
    dsimp [b']
    group
  obtain ⟨v,hv,hvb⟩ := fixed_coset_lift s u hu hf
  let d := w⁻¹*v⁻¹*u*w*b'
  have hd : d ∈ borel P := mul_mem hvb hb'
  have hgd : g = v*w*d := by rw [he']; dsimp [d]; group
  have hdN : d ∈ normalizer (torus P : Set C) := by
    have hh := (normalizer (torus P : Set C)).mul_mem
      ((normalizer (torus P : Set C)).inv_mem
        ((normalizer (torus P : Set C)).mul_mem (centralizer_le_normalizer _ hv.2) hw)) hn
    convert hh using 1
    rw [hgd]
    group
  exact ⟨v,hv,d,⟨hd,hdN⟩,hgd⟩

/-- The fixed long-root product, as an element of the full native Borel. -/
def fixedBorel (a : Fin 3 → fixedField P) : borel P :=
  ⟨CentralCovers.TwoPrimary.baseProduct 1 Nat.zero_lt_one (0,a),
    unipotent_le_borel P
      ((BinaryTorusCentralizer.mem_unipotent_torus_centralizer_iff _).mpr ⟨a,rfl⟩).1⟩

/-- The native torus included in the same Borel. -/
def torusBorel (t : torus P) : borel P := ⟨t,torus_le_borel P t.property⟩

/-- The fixed simple reflection in its actual endpoint subgroup. -/
def simpleEndpoint (s : Node) : parabolic P s :=
  ⟨simpleRepresentative P rfl s,simpleRepresentative_mem_parabolic P rfl s⟩

/-- Exact native coordinates for a torus-normalizing endpoint element. -/
def endpointWord (s : Node) (a b : Fin 3 → fixedField P) (t : torus P) :
    parabolic P s :=
  inclusion (borel_le_parabolic P s) (fixedBorel a) * simpleEndpoint s *
    inclusion (borel_le_parabolic P s) (fixedBorel b) *
    inclusion (borel_le_parabolic P s) (torusBorel t)

@[simp] theorem endpointWord_val (s : Node) (a b : Fin 3 → fixedField P) (t : torus P) :
    (endpointWord s a b t : C) =
      CentralCovers.TwoPrimary.baseProduct 1 Nat.zero_lt_one (0,a) * simpleRepresentative P rfl s *
        CentralCovers.TwoPrimary.baseProduct 1 Nat.zero_lt_one (0,b) * t := rfl

/-- Coprime fixed-coset lifting reduces each endpoint normalizer to the
three binary long-root coordinates on either side of its simple reflection. -/
theorem normalizing_endpoint_coordinates (s : Node) (g : parabolic P s)
    (hout : (g : C) ∉ borel P) (hn : (g : C) ∈ normalizer (torus P : Set C)) :
    ∃ a b : Fin 3 → fixedField P, ∃ t : torus P, g = endpointWord s a b t := by
  obtain ⟨v,hv,b,hb,he⟩ := normalizing_endpoint_factors s g g.property hout hn
  obtain ⟨a,ha⟩ := (BinaryTorusCentralizer.mem_unipotent_torus_centralizer_iff v).mp hv
  obtain ⟨⟨u,t⟩,hut',_⟩ := existsUnique_borel_factors P rfl ⟨b,hb.1⟩
  change (u : C)*t=b at hut'
  have huN : (u : C) ∈ normalizer (torus P : Set C) := by
    have hh := (normalizer _).mul_mem hb.2
      ((torus P).le_normalizer ((torus P).inv_mem t.property))
    simpa only [←hut',mul_inv_cancel_right] using hh
  have huC : (u : C) ∈ unipotent P ⊓ centralizer (torus P : Set C) :=
    BinaryTorusCentralizer.unipotent_normalizer_eq_centralizer ▸ ⟨u.property,huN⟩
  obtain ⟨d,hd⟩ := (BinaryTorusCentralizer.mem_unipotent_torus_centralizer_iff u).mp huC
  refine ⟨a,d,t,Subtype.ext ?_⟩
  simp only [endpointWord_val,he,←ha,hd,←hut',mul_assoc]


private theorem fixed_unipotent_le_arms_radical :
    unipotent P ⊓ centralizer (torus P : Set C) ≤ radical P .arms := by
  intro g hg
  obtain ⟨a,rfl⟩ := (BinaryTorusCentralizer.mem_unipotent_torus_centralizer_iff g).mp hg
  simp only [CentralCovers.TwoPrimary.baseProduct, Pi.zero_apply, short_zero P rfl, one_mul, mul_one]
  apply mul_mem (mul_mem ?_ ?_) ?_
  all_goals
    exact RadicalCoordinates.descendedRootSubgroup_le_radical P rfl .arms
      (RadicalCoordinates.LeviCommutators.long_mem P rfl .arms _ trivial _)

private theorem arms_radical_le_unipotent : radical P .arms ≤ unipotent P := by
  rw [RadicalCoordinates.radical_eq_descendedRootSubgroup P rfl .arms]
  exact descendSubgroup_mono P (RadicalCoordinates.rootSubgroup_le_positiveSubgroup P rfl .arms)

private theorem arms_reflection_fixed_unipotent (u : C)
    (hu : u ∈ unipotent P ⊓ centralizer (torus P : Set C)) :
    simpleRepresentative P rfl .arms * u * (simpleRepresentative P rfl .arms)⁻¹ ∈
      unipotent P ⊓ centralizer (torus P : Set C) := by
  constructor
  · apply arms_radical_le_unipotent
    exact (mem_normalizer_iff.mp
      ((normal_subgroupOf_iff_le_normalizer (radical_le_parabolic P .arms)).mp
        (radical_normal P .arms) (simpleRepresentative_mem_parabolic P rfl .arms)) u).mp
          (fixed_unipotent_le_arms_radical hu)
  · exact (normal_subgroupOf_iff (centralizer_le_normalizer (torus P : Set C))).mp
      (normal_subgroupOf_centralizer_normalizer (torus P : Set C))
      u (simpleRepresentative P rfl .arms) hu.2 (reflection_normalizes .arms)

private theorem baseProduct_zero :
    CentralCovers.TwoPrimary.baseProduct 1 Nat.zero_lt_one (0,0) = 1 := by
  simp only [CentralCovers.TwoPrimary.baseProduct, Pi.zero_apply,
    RadicalCoordinates.LeviCommutators.short_zero P rfl,
    RadicalCoordinates.LeviCommutators.long_zero P rfl, one_mul]

/-- At the arms endpoint the reflection preserves the entire fixed unipotent
group, so only one three-coordinate correction is needed. -/
theorem arms_normalizing_coordinates (g : parabolic P .arms)
    (hout : (g : C) ∉ borel P) (hn : (g : C) ∈ normalizer (torus P : Set C)) :
    ∃ a : Fin 3 → fixedField P, ∃ t : torus P, g = endpointWord .arms a 0 t := by
  obtain ⟨a,b,t,he⟩ := normalizing_endpoint_coordinates .arms g hout hn
  let v := (fixedBorel a : C)
  let u := (fixedBorel b : C)
  let w := simpleRepresentative P rfl .arms
  have hv : v ∈ unipotent P ⊓ centralizer (torus P : Set C) :=
    (BinaryTorusCentralizer.mem_unipotent_torus_centralizer_iff v).mpr ⟨a,rfl⟩
  have hu : u ∈ unipotent P ⊓ centralizer (torus P : Set C) :=
    (BinaryTorusCentralizer.mem_unipotent_torus_centralizer_iff u).mpr ⟨b,rfl⟩
  have hz := (unipotent P ⊓ centralizer (torus P : Set C)).mul_mem hv
    (arms_reflection_fixed_unipotent u hu)
  obtain ⟨d,hd⟩ := (BinaryTorusCentralizer.mem_unipotent_torus_centralizer_iff _).mp hz
  refine ⟨d,t,Subtype.ext ?_⟩
  rw [he,endpointWord_val,endpointWord_val,baseProduct_zero,mul_one,hd]
  change v*w*u*t = (v*(w*u*w⁻¹))*w*t
  group

open EvenInvolutionGeometry.ArmsNormalization

private theorem fixed_product (a : Fin 3 → fixedField P) :
    CentralCovers.TwoPrimary.baseProduct 1 Nat.zero_lt_one (0,a) =
      long P rfl 0 (a 0) * long P rfl 1 (a 1) * long P rfl 2 (a 2) := by
  simp only [CentralCovers.TwoPrimary.baseProduct,Pi.zero_apply,short_zero P rfl,one_mul,mul_one]

private theorem leading_product (a : fixedField P) :
    CentralCovers.TwoPrimary.baseProduct 1 Nat.zero_lt_one (0,Pi.single 0 a) =
      long P rfl 0 a := by
  simp [fixed_product,long_zero P rfl]

private theorem long_fixed (i : Fin 3) (a : fixedField P) :
    long P rfl i a ∈ unipotent P ⊓ centralizer (torus P : Set C) := by
  refine ⟨?_,BinaryTorusCentralizer.long_mem_torus_centralizer i a⟩
  exact descendSubgroup_mono P (RadicalCoordinates.rootSubgroup_le_positiveSubgroup P rfl .arms)
    (long_mem P rfl .arms i trivial a)

private theorem central_tail (a b : fixedField P) :
    (simpleRepresentative P rfl .central)⁻¹ *
      (long P rfl 1 a * long P rfl 2 b) * simpleRepresentative P rfl .central =
        long P rfl 2 a * long P rfl 1 b := by
  have hi : (simpleRepresentative P rfl .central)⁻¹ = simpleRepresentative P rfl .central :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using simpleRepresentative_sq P rfl .central)
  calc
    _ = simpleRepresentative P rfl .central * (long P rfl 1 a * long P rfl 2 b) *
        (simpleRepresentative P rfl .central)⁻¹ := by rw [hi]
    _ = (simpleRepresentative P rfl .central * long P rfl 1 a *
        (simpleRepresentative P rfl .central)⁻¹) *
        (simpleRepresentative P rfl .central * long P rfl 2 b *
          (simpleRepresentative P rfl .central)⁻¹) := by group
    _ = _ := by
      rw [←weylRepresentative_simple P rfl .central]
      exact congrArg₂ (· * ·) (central_long_one P rfl a) (central_long_two P rfl b)

/-- At the central endpoint only the simple long-root coordinate is needed
before the reflection. The other two long roots are moved to the right. -/
theorem central_normalizing_coordinates (g : parabolic P .central)
    (hout : (g : C) ∉ borel P) (hn : (g : C) ∈ normalizer (torus P : Set C)) :
    ∃ a : fixedField P, ∃ b : Fin 3 → fixedField P, ∃ t : torus P,
      g = endpointWord .central (Pi.single 0 a) b t := by
  obtain ⟨a,b,t,he⟩ := normalizing_endpoint_coordinates .central g hout hn
  let v := long P rfl 1 (a 1) * long P rfl 2 (a 2)
  let u := (fixedBorel b : C)
  let w := simpleRepresentative P rfl .central
  have hu : u ∈ unipotent P ⊓ centralizer (torus P : Set C) :=
    (BinaryTorusCentralizer.mem_unipotent_torus_centralizer_iff u).mpr ⟨b,rfl⟩
  have hv : w⁻¹*v*w ∈ unipotent P ⊓ centralizer (torus P : Set C) := by
    rw [show w⁻¹*v*w = long P rfl 2 (a 1) * long P rfl 1 (a 2) from central_tail _ _]
    exact mul_mem (long_fixed _ _) (long_fixed _ _)
  obtain ⟨d,hd⟩ := (BinaryTorusCentralizer.mem_unipotent_torus_centralizer_iff _).mp
    ((unipotent P ⊓ centralizer (torus P : Set C)).mul_mem hv hu)
  refine ⟨a 0,d,t,Subtype.ext ?_⟩
  rw [he,endpointWord_val,endpointWord_val,leading_product,hd,fixed_product a]
  change long P rfl 0 (a 0) * long P rfl 1 (a 1) * long P rfl 2 (a 2) * w * u * t =
    long P rfl 0 (a 0) * w * ((w⁻¹*v*w)*u) * t
  dsimp only [v]
  group

end Triality.Standard.BinaryTorusEndpoints
