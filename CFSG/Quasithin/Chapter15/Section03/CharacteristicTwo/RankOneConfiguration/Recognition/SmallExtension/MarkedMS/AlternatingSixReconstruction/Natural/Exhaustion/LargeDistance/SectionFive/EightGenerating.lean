module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightLarge
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightBaumann
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowShiftChain
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightStrictShift
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightSmallMovers
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubePaths
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowCompatible
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightSelection
/-!
# Generating small-image shifts for the actual image-eight radical

The paired selection must generate with each endpoint separately, since
trapping may choose either orientation. In the canonical Sylow group, write
J = E intersect D for the three-duad mover. Its square and a permutation moving
the final pair provide short certificates for paired generation and membership
of one order-three transporter in the two movers. The two endpoint
transpositions also each generate S6 with E: an element of the Sylow group
exchanges them and normalizes its index-two subgroup E.

Lifting these identities through the entire quotient kernel gives one actual
edge core which generates with each full endpoint seed. The paired trapping
argument retains generation when it pulls the second orientation back to the
original path. The unequal-mover branch retains its already constructed edge
generation. Strict forward slices then construct a generating backward shift
for every small critical image. Together with EightLarge this supplies such a
shift for every critical path above distance four, retaining a single element
on both initial vertices and all overlapping vertices.

Two shifts yield both critical indices two and a noncentral commutator line.
The original-radical application preserves its literal restriction and index
two over the transported replacement edge core. Both moved covers and their
full central attachments remain. Terminal mover comparisons and the source
(5.11) contradiction still require proof.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.5)--(5.10), printed pp.917--923. The finite coordinates use the
six-letter offender models of Aschbacher--Smith B.3.2--4. The private imports
reuse the existing canonical model and quotient transport proofs.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightGenerating
local notation "S" => Equiv.Perm (Fin 6)
open CubeCommonFixer
private abbrev a : S := Equiv.swap 0 1
private abbrev b : S := Equiv.swap 2 3
private abbrev c : S := Equiv.swap 4 5
private abbrev z : S := a*b
private abbrev t : S := Equiv.swap 0 4
private def r : S := ⟨![2,0,1,4,5,3], ![1,2,0,5,3,4], by decide +kernel, by decide +kernel⟩
private abbrev k : S := Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 4 5
private def y (m : Fin 2) : S := if m=0 then c else a*c

private theorem canonical_pair (E : Subgroup S) (hES : E ≤ sylowCarrier)
    (hE : Nat.card E = 8) (hne : ¬ IsElementaryAbelian 2 E)
    (hy : ∃ w ∈ E ⊓ D 6, w (4 : Fin 6) ≠ 4) :
    let J := E ⊓ D 6
    J ⊔ zpowers t ⊔ zpowers ((MulAut.conj r) t) = ⊤ ∧
    r⁻¹ ∈ J ⊔ J.map (MulAut.conj r⁻¹).toMonoidHom ∧
    E ⊔ zpowers t = ⊤ ∧ E ⊔ zpowers ((MulAut.conj r) t) = ⊤ := by
  let J := E ⊓ D 6
  have hex : ∃ x ∈ E, x^2 ≠ 1 := by
    by_contra! hh
    exact hne (NonsylowImage.elementary_of_squares E hh)
  obtain ⟨x,hx,hsq⟩ := hex
  obtain ⟨i,rfl⟩ := (mem_sylowCarrier_iff _).mp (hES hx)
  have hz : z ∈ J := by
    have he := (NonsylowImage.sylow_square_certificate i).resolve_left hsq
    change (sylowWords i)^2=z at he
    exact ⟨he ▸ E.pow_mem hx 2,(mem_disjointTranspositions_iff (3 : Fin 4) _).mpr ⟨3,by decide +kernel⟩⟩
  have hy₀ := hy
  obtain ⟨w,hw,hw4⟩ := hy
  obtain ⟨j,rfl⟩ := (mem_disjointTranspositions_iff (3 : Fin 4) _).mp hw.2
  obtain ⟨m,hm⟩ : ∃ m : Fin 2, y m ∈ J := by
    have cert : ∀ j : Fin 8, dWords j (4 : Fin 6) ≠ 4 →
        ∃ m : Fin 2, y m = dWords j ∨ y m = z*dWords j := by decide +kernel
    obtain ⟨m,he | he⟩ := cert j hw4
    · exact ⟨m,he ▸ hw⟩
    · exact ⟨m,he ▸ J.mul_mem hz hw⟩
  have hgen : E ⊔ zpowers t = ⊤ := EightStrictShift.canonical_generates E hES hne hy₀
  refine ⟨?_,?_,hgen,?_⟩
  · let N := J ⊔ zpowers t ⊔ zpowers ((MulAut.conj r) t)
    have hZ : z ∈ N := mem_sup_left (mem_sup_left hz)
    have hY : y m ∈ N := mem_sup_left (mem_sup_left hm)
    have hT : t ∈ N := mem_sup_left (mem_sup_right (mem_zpowers _))
    have hR : (MulAut.conj r) t ∈ N := mem_sup_right (mem_zpowers _)
    apply chain_generates (1 : S)
    intro j
    change Equiv.swap j.castSucc j.succ ∈ N
    fin_cases j
    · change Equiv.swap (0 : Fin 6) 1 ∈ N
      have he : ∀ m : Fin 2, (t)*(z)*(t)*(z)*(t) = Equiv.swap 0 1 := by decide +kernel
      rw [←he m]
      exact N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (hT) hZ) hT) hZ) hT
    · change Equiv.swap (1 : Fin 6) 2 ∈ N
      fin_cases m
      · have he : ((MulAut.conj r) t)*(z)*(y 0)*(t)*(z)*(y 0)*((MulAut.conj r) t) = Equiv.swap 1 2 := by decide +kernel
        rw [←he]
        exact N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (hR) hZ) hY) hT) hZ) hY) hR
      · have he : ((MulAut.conj r) t)*(y 1)*(t)*(y 1)*((MulAut.conj r) t) = Equiv.swap 1 2 := by decide +kernel
        rw [←he]
        exact N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (hR) hY) hT) hY) hR
    · change Equiv.swap (2 : Fin 6) 3 ∈ N
      have he : ∀ m : Fin 2, ((MulAut.conj r) t)*(z)*((MulAut.conj r) t)*(z)*((MulAut.conj r) t) = Equiv.swap 2 3 := by decide +kernel
      rw [←he m]
      exact N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (hR) hZ) hR) hZ) hR
    · change Equiv.swap (3 : Fin 6) 4 ∈ N
      have he : ∀ m : Fin 2, (z)*(y m)*((MulAut.conj r) t)*(z)*(y m) = Equiv.swap 3 4 := by decide +kernel
      rw [←he m]
      exact N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (hZ) hY) hR) hZ) hY
    · change Equiv.swap (4 : Fin 6) 5 ∈ N
      fin_cases m
      · have he : (y 0) = Equiv.swap 4 5 := by decide +kernel
        rw [←he]
        exact hY
      · have he : ((MulAut.conj r) t)*(y 1)*((MulAut.conj r) t)*(y 1)*((MulAut.conj r) t) = Equiv.swap 4 5 := by decide +kernel
        rw [←he]
        exact N.mul_mem (N.mul_mem (N.mul_mem (N.mul_mem (hR) hY) hR) hY) hR
  · let N := J ⊔ J.map (MulAut.conj r⁻¹).toMonoidHom
    have hZ : z ∈ N := mem_sup_left hz
    have hY : y m ∈ N := mem_sup_left hm
    have hZ' : (MulAut.conj r⁻¹) z ∈ N := mem_sup_right (mem_map_of_mem _ hz)
    have hY' : (MulAut.conj r⁻¹) (y m) ∈ N := mem_sup_right (mem_map_of_mem _ hm)
    fin_cases m
    · have he : (z)*(y 0)*((MulAut.conj r⁻¹) (y 0))*(z)*((MulAut.conj r⁻¹) z)*(y 0)*((MulAut.conj r⁻¹) z)*((MulAut.conj r⁻¹) (y 0))*(z) = r⁻¹ := by ext i; fin_cases i <;> rfl
      have step0 := N.mul_mem hZ hY
      have step1 := N.mul_mem step0 hY'
      have step2 := N.mul_mem step1 hZ
      have step3 := N.mul_mem step2 hZ'
      have step4 := N.mul_mem step3 hY
      have step5 := N.mul_mem step4 hZ'
      have step6 := N.mul_mem step5 hY'
      have step7 := N.mul_mem step6 hZ
      exact (congrArg (fun w : S => w ∈ N) he).mp step7
    · have he : (y 1)*((MulAut.conj r⁻¹) (y 1)) = r⁻¹ := by ext i; fin_cases i <;> rfl
      have step0 := N.mul_mem hY hY'
      exact (congrArg (fun w : S => w ∈ N) he).mp step0
  · have hindex : E.relIndex sylowCarrier = 2 := by
      have hh := relIndex_mul_relIndex (⊥ : Subgroup S) E sylowCarrier bot_le hES
      rw [relIndex_bot_left,relIndex_bot_left,hE,card_sylowCarrier] at hh
      omega
    let : (E.subgroupOf sylowCarrier).Normal := normal_of_index_eq_two hindex
    have hk : k ∈ sylowCarrier := (mem_sylowCarrier_iff _).mpr (by decide +kernel)
    have hkn : k ∈ normalizer (E : Set S) := by
      apply mem_normalizer_iff.mpr
      intro w
      constructor
      · intro hw
        exact (inferInstance : (E.subgroupOf sylowCarrier).Normal).conj_mem
          ⟨w,hES hw⟩ hw ⟨k,hk⟩
      · intro hw
        have hh := (inferInstance : (E.subgroupOf sylowCarrier).Normal).conj_mem
          ⟨k*w*k⁻¹,hES hw⟩ hw ⟨k⁻¹,sylowCarrier.inv_mem hk⟩
        change k⁻¹*(k*w*k⁻¹)*(k⁻¹)⁻¹ ∈ E at hh
        have he : k⁻¹*(k*w*k⁻¹)*(k⁻¹)⁻¹ = w := by group
        rwa [he] at hh
    have hmap : E.map (MulAut.conj k).toMonoidHom = E :=
      mem_normalizer_iff_map_conj_eq.mp hkn
    have hh := congrArg (Subgroup.map (MulAut.conj k).toMonoidHom) hgen
    rw [Subgroup.map_sup,hmap,
      MonoidHom.map_zpowers,map_top_of_surjective _ (MulAut.conj k).surjective] at hh
    have he : (MulAut.conj k).toMonoidHom t = (MulAut.conj r) t := by decide +kernel
    rwa [he] at hh
private theorem compatible_pair (E J : Subgroup S) (u : S)
    (hES : E ≤ sylowCarrier.map (MulAut.conj u).toMonoidHom)
    (hEcard : Nat.card E = 8) (hne : ¬ IsElementaryAbelian 2 E)
    (hJ : J = E ⊓ (D 6).map (MulAut.conj u).toMonoidHom)
    (hmodel : IsConjugateTo J plus ∨ IsConjugateTo J (evenPart 6))
    (v : S) (hv : v.IsSwap) :
    ∃ w x : S, x ∈ alternatingGroup (Fin 6) ∧ orderOf x = 3 ∧
      let J₁ := J.map (MulAut.conj w).toMonoidHom
      let E₁ := E.map (MulAut.conj w).toMonoidHom
      J₁ ⊔ zpowers v ⊔ zpowers ((MulAut.conj x) v) = ⊤ ∧
      x⁻¹ ∈ J₁ ⊔ J₁.map (MulAut.conj x⁻¹).toMonoidHom ∧
      E₁ ⊔ zpowers v = ⊤ ∧ E₁ ⊔ zpowers ((MulAut.conj x) v) = ⊤ := by
  let f := (MulAut.conj u⁻¹).toMonoidHom
  have back (A : Subgroup S) : (A.map (MulAut.conj u).toMonoidHom).map f = A := by
    rw [conjugate_twice,inv_mul_cancel,
      show (MulAut.conj (1 : S)).toMonoidHom = MonoidHom.id S from rfl,map_id]
  have hE : E.map f ≤ sylowCarrier := (map_mono hES).trans_eq (back _)
  have hn : ¬ IsElementaryAbelian 2 (E.map f) := by
    intro hh
    let := hh
    apply hne
    apply NonsylowImage.elementary_of_squares
    intro x hx
    apply (MulAut.conj u⁻¹).injective
    rw [map_pow,map_one]
    exact elemPow_eq_one_of_isElementaryAbelian _ (mem_map_of_mem f hx)
  have hJF : J.map f = E.map f ⊓ D 6 := by
    rw [hJ,map_inf _ _ _ (MulAut.conj u⁻¹).injective,back]
  obtain ⟨m,r₀,hr⟩ : ∃ m : Fin 2, ∃ r₀ : S,
      J = (EightSelection.model m).map (MulAut.conj r₀).toMonoidHom := by
    rcases hmodel with ⟨r,hr⟩ | ⟨r,hr⟩
    · exact ⟨0,r,hr⟩
    · exact ⟨1,r,hr⟩
  have hmove : ∃ y ∈ E.map f ⊓ D 6, y (4 : Fin 6) ≠ 4 := by
    rw [←hJF,hr,conjugate_twice]
    exact EightStrictShift.model_moves m (u⁻¹*r₀) 4
  have hcard : Nat.card (E.map f) = 8 := by
    rw [card_map_of_injective (MulAut.conj u⁻¹).injective,hEcard]
  obtain ⟨hgen,hpair,hleft,hright⟩ := canonical_pair (E.map f) hE hcard hn hmove
  rw [←hJF] at hgen hpair
  obtain ⟨v₀,hv₀⟩ := swap_conjugator v hv
  let k₀ : S := v₀.val * Equiv.swap 1 4
  have hk : (MulAut.conj k₀).toMonoidHom t = v := by
    have cert : (MulAut.conj (Equiv.swap (1 : Fin 6) 4)) t = a := by decide +kernel
    change (MulAut.conj v₀.val) ((MulAut.conj (Equiv.swap 1 4)) t) = v
    rw [cert]
    exact hv₀
  let x := (MulAut.conj k₀) r
  have hx : x ∈ alternatingGroup (Fin 6) :=
    (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem r (by decide +kernel) k₀
  have ht : (MulAut.conj k₀).toMonoidHom ((MulAut.conj r) t) = (MulAut.conj x) v := by
    rw [←hk]
    change k₀*(r*t*r⁻¹)*k₀⁻¹ = (k₀*r*k₀⁻¹)*(k₀*t*k₀⁻¹)*(k₀*r*k₀⁻¹)⁻¹
    group
  have hJx : ((J.map f).map (MulAut.conj r⁻¹).toMonoidHom).map (MulAut.conj k₀).toMonoidHom =
      ((J.map f).map (MulAut.conj k₀).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom := by
    rw [conjugate_twice (J.map f),conjugate_twice (J.map f)]
    have he : k₀*r⁻¹=x⁻¹*k₀ := by change k₀*r⁻¹=(k₀*r*k₀⁻¹)⁻¹*k₀; group
    rw [he]
  refine ⟨k₀*u⁻¹,x,hx,((MulAut.conj k₀).orderOf_eq r).trans
    (orderOf_eq_prime (by decide +kernel) (by decide +kernel)),?_,?_,?_,?_⟩
  · have hh := congrArg (Subgroup.map (MulAut.conj k₀).toMonoidHom) hgen
    simpa only [Subgroup.map_sup,MonoidHom.map_zpowers,hk,ht,f,conjugate_twice,
      map_top_of_surjective (MulAut.conj k₀).toMonoidHom (MulAut.conj k₀).surjective] using hh
  · have hh := mem_map_of_mem (MulAut.conj k₀).toMonoidHom hpair
    rw [Subgroup.map_sup,hJx] at hh
    have hri : (MulAut.conj k₀).toMonoidHom r⁻¹ = x⁻¹ := (MulAut.conj k₀).map_inv r
    simpa only [hri,f,conjugate_twice] using hh
  · have hh := congrArg (Subgroup.map (MulAut.conj k₀).toMonoidHom) hleft
    simpa only [Subgroup.map_sup,MonoidHom.map_zpowers,hk,f,conjugate_twice,
      map_top_of_surjective (MulAut.conj k₀).toMonoidHom (MulAut.conj k₀).surjective] using hh
  · have hh := congrArg (Subgroup.map (MulAut.conj k₀).toMonoidHom) hright
    simpa only [Subgroup.map_sup,MonoidHom.map_zpowers,ht,f,conjugate_twice,
      map_top_of_surjective (MulAut.conj k₀).toMonoidHom (MulAut.conj k₀).surjective] using hh

private theorem compatible_lifts {H : Type*} [Group H]
    (π : H →* S) (hs : Function.Surjective π) (E J C A : Subgroup H)
    (hC : C.map π = alternatingGroup (Fin 6)) (hkJ : π.ker ≤ J)
    (hJE : J ≤ E) (u : S)
    (hES : E.map π ≤ sylowCarrier.map (MulAut.conj u).toMonoidHom)
    (hE : Nat.card (E.map π) = 8) (hne : ¬ IsElementaryAbelian 2 (E.map π))
    (hJimage : J.map π = E.map π ⊓ (D 6).map (MulAut.conj u).toMonoidHom)
    (hmodel : IsConjugateTo (J.map π) plus ∨ IsConjugateTo (J.map π) (evenPart 6))
    (a : S) (ha : a ∈ A.map π) (hswap : a.IsSwap) :
    ∃ g y : H, y ∈ C ∧ y^3 ∈ π.ker ∧
      let J₁ := J.map (MulAut.conj g).toMonoidHom
      let A₁ := A.map (MulAut.conj y).toMonoidHom
      J₁ ⊔ A ⊔ A₁ = ⊤ ∧ y⁻¹ ∈ J₁ ⊔ J₁.map (MulAut.conj y⁻¹).toMonoidHom ∧
      E.map (MulAut.conj g).toMonoidHom ⊔ A = ⊤ ∧
      E.map (MulAut.conj g).toMonoidHom ⊔ A₁ = ⊤ := by
  obtain ⟨v,b',hb,hbo,hgen,hpair,hleft,hright⟩ :=
    compatible_pair (E.map π) (J.map π) u hES hE hne hJimage hmodel a hswap
  obtain ⟨g,hg⟩ := hs v
  have hbL : b' ∈ C.map π := hC.symm ▸ hb
  obtain ⟨y,hy,hyb⟩ := hbL
  let J₁ := J.map (MulAut.conj g).toMonoidHom
  let E₁ := E.map (MulAut.conj g).toMonoidHom
  let A₁ := A.map (MulAut.conj y).toMonoidHom
  have hJ : J₁.map π = (J.map π).map (MulAut.conj v).toMonoidHom := by
    rw [SylowCompatible.image_conjugate,hg]
  have hEE : E₁.map π = (E.map π).map (MulAut.conj v).toMonoidHom := by
    rw [SylowCompatible.image_conjugate,hg]
  have hker : π.ker.map (MulAut.conj g).toMonoidHom = π.ker :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  have hkJ₁ : π.ker ≤ J₁ := by rw [←hker]; exact map_mono hkJ
  have hA₁ : A₁.map π = (A.map π).map (MulAut.conj b').toMonoidHom := by
    rw [SylowCompatible.image_conjugate,hyb]
  have htop : J₁ ⊔ A ⊔ A₁ = ⊤ := by
    apply map_injective_of_ker_le π (hkJ₁.trans (le_sup_left.trans le_sup_left)) le_top
    rw [Subgroup.map_sup,Subgroup.map_sup,hJ,hA₁,map_top_of_surjective π hs]
    apply top_unique
    rw [←hgen]
    exact sup_le_sup (sup_le_sup_left (zpowers_le.mpr ha) _)
      (zpowers_le.mpr (mem_map_of_mem (MulAut.conj b').toMonoidHom ha))
  have hyP : y⁻¹ ∈ J₁ ⊔ J₁.map (MulAut.conj y⁻¹).toMonoidHom := by
    have hh : y⁻¹ ∈ ((J₁ ⊔ J₁.map (MulAut.conj y⁻¹).toMonoidHom).map π).comap π := by
      change π (y⁻¹) ∈ (J₁ ⊔ J₁.map (MulAut.conj y⁻¹).toMonoidHom).map π
      rw [Subgroup.map_sup,SylowCompatible.image_conjugate π J₁ y⁻¹,map_inv,hyb,hJ]
      exact hpair
    rwa [comap_map_eq,sup_eq_left.mpr (hkJ₁.trans le_sup_left)] at hh
  have hkE₁ : π.ker ≤ E₁ := hkJ₁.trans (map_mono hJE)
  have lift_gen (D : Subgroup H) (w : S) (hw : w ∈ D.map π)
      (hgen : (E.map π).map (MulAut.conj v).toMonoidHom ⊔ zpowers w = ⊤) :
      E₁ ⊔ D = ⊤ := by
    apply map_injective_of_ker_le π (hkE₁.trans le_sup_left) le_top
    rw [Subgroup.map_sup,hEE,map_top_of_surjective π hs]
    apply top_unique
    rw [←hgen]
    exact sup_le_sup_left (zpowers_le.mpr hw) _
  refine ⟨g,y,hy,?_,htop,hyP,lift_gen A a ha hleft,lift_gen A₁ ((MulAut.conj b') a) ?_ hright⟩
  · rw [MonoidHom.mem_ker,map_pow,hyb]
    simpa only [hbo] using pow_orderOf_eq_one b'
  · rw [hA₁]
    exact mem_map_of_mem _ ha

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- Choose one edge kernel generating with each of the two endpoint seeds,
while the same residual transporter belongs to the paired movers. -/
theorem paired_generating_selection_knownSimple
    (hb : 4 < replacementDistance h d) (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4) :
    ∃ g ∈ stabilizer d.radical (alpha d.radical),
      ∃ x ∈ Ltilde d.radical (alpha d.radical),
        x^3 ∈ Q d.radical (alpha d.radical) ∧
        let t := act d.radical g (beta d.radical)
        let J := EightEdgeComparison.edgeMover (d := d) (alpha d.radical) t
        Adjacent d.radical (alpha d.radical) t ∧
          J ⊔ Z d.radical z ⊔ Z d.radical (act d.radical x z) =
            stabilizer d.radical (alpha d.radical) ∧
          x ∈ J ⊔ J.map (MulAut.conj x).toMonoidHom ∧
          Q d.radical t ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) ∧
          Q d.radical t ⊔ Z d.radical (act d.radical x z) =
            stabilizer d.radical (alpha d.radical) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let J₀ := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4
  obtain ⟨u,hN,_,_,hJimage,_,_,_,_⟩ := EightSmallMovers.radical_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  obtain ⟨_,hne,_,hE⟩ := SylowWholeCore.four_lt_original_sylow_eight_image_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  rw [←SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at hne hE
  have hmodel' : IsConjugateTo (J₀.map s.projection) plus ∨
      IsConjugateTo (J₀.map s.projection) (evenPart 6) := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hkJ : s.projection.ker ≤ J₀ := by
    rw [s.projection_kernel]
    let := replacementMoved_normal h d
    exact SmallMover.kernel_le_join _ _ _ 4 (by decide) (replacement_core_le_radical h d)
      (by rw [←moved_centralizer s]; exact le_centralizer_iff.mpr le_rfl)
  obtain ⟨a,ha,hswap⟩ := small_critical_image_swap s hc p hsmall
  let A := (Z d.radical z).comap (embedM d.radical)
  obtain ⟨g,y,hy,hy3,htop,hpair,hleft,hright⟩ := compatible_lifts s.projection s.surjective
    d.radical J₀ (replacementComponent d) A s.component_image hkJ
    (sSup_le fun _ hB => hB.1.1) u ((map_mono d.radical.le_normalizer).trans_eq hN)
    hE hne hJimage hmodel' a ha hswap
  let J₁ := J₀.map (MulAut.conj g).toMonoidHom
  let A₁ := A.map (MulAut.conj y).toMonoidHom
  have hQ : (pCore 2 d.overgroup).map (MulAut.conj g).toMonoidHom = pCore 2 d.overgroup :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  have hU : (replacementMoved d).map (MulAut.conj g).toMonoidHom = replacementMoved d := by
    let := replacementMoved_normal h d
    exact mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  let f := (embedM d.radical g)⁻¹
  let x := (embedM d.radical y)⁻¹
  let t := act d.radical f (beta d.radical)
  let J := EightEdgeComparison.edgeMover (d := d) (alpha d.radical) t
  have hf : f ∈ stabilizer d.radical (alpha d.radical) := by
    change f ∈ stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    exact ⟨g⁻¹,by simp only [map_inv,f]⟩
  have ht : Q d.radical t = (d.radical.map (MulAut.conj g).toMonoidHom).map (embedM d.radical) := by
    rw [Q_act,Q_beta,SylowCompatible.image_conjugate]
    simp only [f,inv_inv]
  have hJm : J₁.map (embedM d.radical) = J := by
    change ((SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4).map
      (MulAut.conj g).toMonoidHom).map (embedM d.radical) = J
    rw [SmallMover.join_map _ (MulAut.conj g).injective,hU,hQ,
      SmallMover.join_map _ (embedM_injective d.radical),←hc.U_eq_moved,
      ←Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d),←ht]
  have hxL : x ∈ Ltilde d.radical (alpha d.radical) := by
    rw [Ltilde_alpha,replacement_residual h d]
    exact mem_map_of_mem _ ((replacementComponent d).inv_mem hy)
  have hAm : A.map (embedM d.radical) = Z d.radical z :=
    map_comap_eq_self ((critical_Z_le_stabilizer d.radical (replacementGeometry h d)
      (alpha d.radical) rfl (replacementDistance_pos h d) p.critical).trans_eq
        (stabilizer_m_base d.radical))
  have hA₁m : A₁.map (embedM d.radical) = Z d.radical (act d.radical x z) := by
    rw [SylowCompatible.image_conjugate,hAm,Z_act]
    simp only [x,inv_inv]
  have hrange : (embedM d.radical).range = stabilizer d.radical (alpha d.radical) :=
    (stabilizer_m_base d.radical).symm
  change y⁻¹ ∈ J₁ ⊔ J₁.map (MulAut.conj y⁻¹).toMonoidHom at hpair
  refine ⟨f,hf,x,hxL,?_,?_,?_,?_,?_,?_⟩
  · rw [s.projection_kernel] at hy3
    rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)]
    have hx3 : x^3=embedM d.radical ((y^3)⁻¹) := by simp only [x,inv_pow,map_inv,map_pow]
    rw [hx3]
    exact mem_map_of_mem _ ((pCore 2 d.overgroup).inv_mem hy3)
  · have hfix : act d.radical f (alpha d.radical)=alpha d.radical := hf
    rw [←hfix]
    exact (adjacent_act_iff d.radical f _ _).mpr (base_adjacent d.radical)
  · have hh := congrArg (Subgroup.map (embedM d.radical)) htop
    rwa [Subgroup.map_sup,Subgroup.map_sup,hJm,hAm,hA₁m,←MonoidHom.range_eq_map,
      hrange] at hh
  · have hh := mem_map_of_mem (embedM d.radical) hpair
    rwa [Subgroup.map_sup,SylowCompatible.image_conjugate (embedM d.radical) J₁ y⁻¹,
      map_inv,hJm] at hh
  · have hh := congrArg (Subgroup.map (embedM d.radical)) hleft
    rwa [Subgroup.map_sup,←ht,hAm,←MonoidHom.range_eq_map,hrange] at hh
  · have hh := congrArg (Subgroup.map (embedM d.radical)) hright
    rwa [Subgroup.map_sup,←ht,hA₁m,←MonoidHom.range_eq_map,hrange] at hh

include e hz hn in
/-- The equal-mover branch of (5.7) now has a constructed selection in both
three-duad cases. The resulting backward path overlaps the original path,
with the selected seed transported by the same starting-stabilizer element. -/
theorem equal_mover_generating_backward_knownSimple
    (hb : 4 < replacementDistance h d) (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (hdelta : Adjacent d.radical delta (beta d.radical))
    (hequal : EightEdgeComparison.edgeMover (d := d) delta (beta d.radical) =
      EightEdgeComparison.edgeMover (d := d) (alpha d.radical) (beta d.radical))
    (hstrict : 2 < (B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical delta)) :
    ∃ g ∈ stabilizer d.radical (alpha d.radical),
      let c := act d.radical g delta
      let t := act d.radical g (beta d.radical)
      Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical c t ∧
        2 < (B d.radical (alpha d.radical)
          ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c) ∧
        Q d.radical t ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d)
            c (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  obtain ⟨g,hg,x,hxL,_,hat,hgen,hxpair,hleft,hright⟩ := paired_generating_selection_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hmodel p hsmall
  let c := act d.radical g delta
  let t := act d.radical g (beta d.radical)
  have hx : x ∈ stabilizer d.radical (alpha d.radical) := Ltilde_le_stabilizer _ hxL
  have hct : Adjacent d.radical c t := (adjacent_act_iff d.radical g _ _).mpr hdelta
  have hga : act d.radical g (alpha d.radical) = alpha d.radical := hg
  have hEq : EightEdgeComparison.edgeMover (d := d) c t =
      EightEdgeComparison.edgeMover (d := d) (alpha d.radical) t := by
    have hh := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hequal
    dsimp only [EightEdgeComparison.edgeMover] at hh ⊢
    rw [SmallMover.join_map _ (MulAut.conj g⁻¹).injective,
      SmallMover.join_map _ (MulAut.conj g⁻¹).injective,←U_act,←Q_act,←Q_act,
      ←U_act,←Q_act,hga] at hh
    exact hh
  have strict (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical (alpha d.radical)) :
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (act d.radical y delta)) := by
    have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
        (MulAut.conj y⁻¹).toMonoidHom =
        B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
      mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
        (by omega : 2 < replacementDistance h d) _ rfl ((stabilizer d.radical _).inv_mem hy))
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj y⁻¹).injective]
    exact hstrict
  have hxa : act d.radical x (alpha d.radical) = alpha d.radical := hx
  obtain ⟨q,hq⟩ : ∃ q : CriticalPath d.radical (replacementGeometry h d)
      (alpha d.radical) (act d.radical x z),
      ∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i) := by
    have hh : ∃ q : CriticalPath d.radical (replacementGeometry h d)
        (act d.radical x (alpha d.radical)) (act d.radical x z),
        ∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i) :=
      ⟨p.act x,fun i => by simp only [CriticalPath.act,actWalk_getVert]⟩
    rwa [hxa] at hh
  have hqs : (Q d.radical (act d.radical x z)).relIndex
      (Z d.radical (alpha d.radical)) < 4 := by
    conv_lhs => rhs; rw [←hxa]
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hsmall
  have hLgen : Ltilde d.radical (alpha d.radical) ≤
      EightEdgeComparison.edgeMover (d := d) c t ⊔ Z d.radical z ⊔
        Z d.radical (act d.radical x z) := by
    rw [hEq,hgen]
    exact Ltilde_le_stabilizer _
  have hcol : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hdelta
    have hc : color d.radical delta = false := by
      change color d.radical delta ≠ true at hh
      cases hc : color d.radical delta <;> simp_all
    change color d.radical (act d.radical g delta) = false
    rw [action_preserves_color,hc]
  have backward {v : Vertex d.radical}
      (b : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) v)
      (hbad : ¬ Z d.radical c ≤ Q d.radical (b.walk.getVert (b.walk.length-2))) :
      ∃ r : CriticalPath d.radical (replacementGeometry h d)
          c (b.walk.getVert (b.walk.length-2)),
        r.walk.getVert 1 = t ∧
        ∀ i ≤ b.walk.length-2, r.walk.getVert (i+2) = b.walk.getVert i := by
    let w : (cosetGraph d.radical).Walk c (alpha d.radical) :=
      .cons ((cosetGraph_adj d.radical _ _).mpr hct)
        (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
    have hw : w.length = 2 := rfl
    have hb2 : 2 ≤ (replacementGeometry h d).b d.radical := by
      change 2 ≤ replacementDistance h d
      omega
    let r := b.prepend_two hb2 hcol w hw hbad
    refine ⟨r,?_,fun i hi => b.prepend_two_overlap _ _ _ _ _ hi⟩
    change (b.prepend_two _ hcol w hw hbad).walk.getVert 1 = t
    rw [CriticalPath.prepend_two_walk]
    simp only [SimpleGraph.Walk.getVert_append,hw,show 1<2 from by decide,ite_true,
      w,SimpleGraph.Walk.getVert_cons_succ,SimpleGraph.Walk.getVert_zero]
  by_cases hpbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2))
  · have hqbad : ¬ Z d.radical c ≤ Q d.radical (q.walk.getVert (q.walk.length-2)) := by
      intro hqbad
      exact EightEdgeComparison.paired_traps_impossible_knownSimple
        (e := e) (hz := hz) (hn := hn) hb p hsmall hat hct hEq x hx q hq
          hqs hLgen hxpair hpbad hqbad (strict g hg)
    obtain ⟨r,hrt,hover⟩ := backward q hqbad
    let y := g*x⁻¹
    have hy : y ∈ stabilizer d.radical (alpha d.radical) := mul_mem hg (inv_mem hx)
    have hstart : act d.radical x⁻¹ c = act d.radical y delta := by
      dsimp only [c,y]
      rw [act_mul]
    have hedge : act d.radical x⁻¹ t = act d.radical y (beta d.radical) := by
      dsimp only [t,y]
      rw [act_mul]
    have hxa' : act d.radical x⁻¹ (alpha d.radical) = alpha d.radical := inv_mem hx
    have hlen : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
    have hend : act d.radical x⁻¹ (q.walk.getVert (q.walk.length-2)) =
        p.walk.getVert (p.walk.length-2) := by
      rw [hlen,hq,←act_mul,mul_inv_cancel,act_one]
    refine ⟨y,hy,?_,?_,strict y hy,?_,?_⟩
    · have hh := (adjacent_act_iff d.radical x⁻¹ _ _).mpr hat
      rwa [hxa',hedge] at hh
    · exact (adjacent_act_iff d.radical y _ _).mpr hdelta
    · have hh := congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hright
      rw [Subgroup.map_sup,←inv_inv x,←Q_act,←Z_act,←stabilizer_act,inv_inv,hxa',hedge,
        ←act_mul,mul_inv_cancel,act_one] at hh
      exact hh
    · have hex : ∃ w : CriticalPath d.radical (replacementGeometry h d)
          (act d.radical x⁻¹ c) (act d.radical x⁻¹ (q.walk.getVert (q.walk.length-2))),
          w.walk.getVert 1 = act d.radical x⁻¹ t ∧
          ∀ i ≤ p.walk.length-2, w.walk.getVert (i+2) = p.walk.getVert i := by
        refine ⟨r.act x⁻¹,?_,?_⟩
        · simp only [CriticalPath.act,actWalk_getVert,hrt]
        · intro i hi
          have hiq : i ≤ q.walk.length-2 := hlen.symm ▸ hi
          simp only [CriticalPath.act,actWalk_getVert,hover i hiq,hq,
            ←act_mul,mul_inv_cancel,act_one]
      rwa [hstart,hend,hedge] at hex
  · exact ⟨g,hg,hat,hct,strict g hg,hleft,backward p hpbad⟩


include e hz hn in
/-- A strict unequal mover has a backward critical path on a constructed
edge; the original vertices and the same seed transporter are retained. -/
theorem unequal_mover_generating_backward_knownSimple
    (hb : 4 < replacementDistance h d) (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (hdelta : Adjacent d.radical delta (beta d.radical))
    (hne : EightEdgeComparison.edgeMover (d := d) delta (beta d.radical) ≠
      EightEdgeComparison.edgeMover (d := d) (alpha d.radical) (beta d.radical))
    (hstrict : 2 < (B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical delta)) :
    ∃ g ∈ stabilizer d.radical (alpha d.radical),
      let c := act d.radical g delta
      let t := act d.radical g (beta d.radical)
      Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical c t ∧
        2 < (B d.radical (alpha d.radical)
          ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c) ∧
        Q d.radical t ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d)
            c (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  obtain ⟨g,hg,hat,hgen⟩ := EightStrictShift.three_duad_generating_edge_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hmodel p hsmall
  let c := act d.radical g delta
  let t := act d.radical g (beta d.radical)
  have hga : act d.radical g (alpha d.radical) = alpha d.radical := hg
  have hct : Adjacent d.radical c t := (adjacent_act_iff d.radical g _ _).mpr hdelta
  have hne' : EightEdgeComparison.edgeMover (d := d) c t ≠
      EightEdgeComparison.edgeMover (d := d) (alpha d.radical) t := by
    intro he
    apply hne
    apply map_injective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective
    dsimp only [EightEdgeComparison.edgeMover] at he ⊢
    rwa [SmallMover.join_map _ (MulAut.conj g⁻¹).injective,
      SmallMover.join_map _ (MulAut.conj g⁻¹).injective,←U_act,←Q_act,←Q_act,
      ←U_act,←Q_act,hga]
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom =
      B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      (by omega : 2 < replacementDistance h d) _ rfl ((stabilizer d.radical _).inv_mem hg))
  have hi : 2 < (B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c) := by
    change 2 < (B d.radical (alpha d.radical) _).relIndex (U d.radical (act d.radical g delta))
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hstrict
  exact ⟨g,hg,hat,hct,hi,hgen,EightUnequalCore.unequal_edge_generating_backward_path_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall hat hct hne' hgen hi⟩

include e hz hn in
/-- Every strict slice has an overlapping backward critical path in the
three-duad branches, with no mover comparison or edge-generation premise. -/
theorem strict_generating_backward_knownSimple
    (hb : 4 < replacementDistance h d) (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (hdelta : Adjacent d.radical delta (beta d.radical))
    (hstrict : 2 < (B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical delta)) :
    ∃ g ∈ stabilizer d.radical (alpha d.radical),
      let c := act d.radical g delta
      let t := act d.radical g (beta d.radical)
      Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical c t ∧
        2 < (B d.radical (alpha d.radical)
          ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c) ∧
        Q d.radical t ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d)
            c (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  by_cases he : EightEdgeComparison.edgeMover (d := d) delta (beta d.radical) =
      EightEdgeComparison.edgeMover (d := d) (alpha d.radical) (beta d.radical)
  · exact equal_mover_generating_backward_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hmodel p hsmall hdelta he hstrict
  · exact unequal_mover_generating_backward_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hmodel p hsmall hdelta he hstrict

include e hz hn in
/-- Strict backward selection for every actual small critical path. The same
starting-stabilizer element transports both of the first two vertices. -/
theorem small_generating_step_knownSimple
    (hb : 4 < replacementDistance h d)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4) :
    ∃ x ∈ stabilizer d.radical a,
      let c := act d.radical x (p.walk.getVert 2)
      let t := act d.radical x (p.walk.getVert 1)
      Adjacent d.radical a t ∧ Adjacent d.radical c t ∧
        2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical c) ∧
        Q d.radical t ⊔ Z d.radical z = stabilizer d.radical a ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d) c
            (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  have hmodel := EightBaumann.three_duad_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  have hl : 4 < p.walk.length := p.length_eq_b ▸ hb
  have ha1 : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have h21 : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨g,hg|hg⟩ := edge_transitive d.radical ha1 (base_adjacent d.radical)
  · change act d.radical g a = alpha d.radical ∧
      act d.radical g (p.walk.getVert 1) = beta d.radical at hg
    have base := strict_generating_backward_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hmodel
      (z := act d.radical g z) (delta := act d.radical g (p.walk.getVert 2))
    rw [←hg.1,←hg.2] at base
    have hsmall' : (Q d.radical (act d.radical g z)).relIndex
        (Z d.radical (act d.radical g a)) < 4 := by
      rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
      exact hsmall
    have hstrict := EightForward.three_duad_small_forward_slice_strict_at_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hmodel (p.act g) hsmall'
    simp only [CriticalPath.act,actWalk_getVert] at hstrict
    obtain ⟨x,hx,hat,hct,hi,hgen,q,hq1,hover⟩ := base (p.act g) hsmall'
      ((adjacent_act_iff d.radical g _ _).mpr h21) hstrict
    let y := g*x*g⁻¹
    have hy (v : Vertex d.radical) :
        act d.radical y v = act d.radical g⁻¹ (act d.radical x (act d.radical g v)) := by
      simp only [y,act_mul]
    have hcancel (v : Vertex d.radical) : act d.radical g⁻¹ (act d.radical g v) = v := by
      rw [←act_mul,mul_inv_cancel,act_one]
    have hqc : ∃ r : CriticalPath d.radical (replacementGeometry h d)
        (act d.radical y (p.walk.getVert 2)) (p.walk.getVert (p.walk.length-2)),
        r.walk.getVert 1 = act d.radical y (p.walk.getVert 1) ∧
        ∀ i ≤ p.walk.length-2, r.walk.getVert (i+2) = p.walk.getVert i := by
      have hh : ∃ r : CriticalPath d.radical (replacementGeometry h d)
          (act d.radical g⁻¹ (act d.radical x (act d.radical g (p.walk.getVert 2))))
          (act d.radical g⁻¹ ((p.act g).walk.getVert ((p.act g).walk.length-2))),
          r.walk.getVert 1 = act d.radical g⁻¹ (act d.radical x (act d.radical g (p.walk.getVert 1))) ∧
          ∀ i ≤ p.walk.length-2, r.walk.getVert (i+2) = p.walk.getVert i := by
        refine ⟨q.act g⁻¹,?_,?_⟩
        · simpa only [CriticalPath.act,actWalk_getVert] using congrArg (act d.radical g⁻¹) hq1
        · intro i hi
          have he := congrArg (act d.radical g⁻¹) (hover i (by
            simpa only [CriticalPath.act,actWalk_length] using hi))
          simpa only [CriticalPath.act,actWalk_getVert,hcancel] using he
      have hend : act d.radical g⁻¹ ((p.act g).walk.getVert ((p.act g).walk.length-2)) =
          p.walk.getVert (p.walk.length-2) := by
        change act d.radical g⁻¹ ((actWalk d.radical g p.walk).getVert
          ((actWalk d.radical g p.walk).length-2)) = _
        rw [actWalk_length,actWalk_getVert,hcancel]
      rw [hend,←hy,←hy] at hh
      exact hh
    refine ⟨y,?_,?_,?_,?_,?_,hqc⟩
    · change act d.radical y a = a
      rw [hy,show act d.radical x (act d.radical g a) = act d.radical g a from hx,hcancel]
    · simpa only [hy,hcancel] using (adjacent_act_iff d.radical g⁻¹ _ _).mpr hat
    · simpa only [hy] using (adjacent_act_iff d.radical g⁻¹ _ _).mpr hct
    · have hBi := Escape.PairingControl.FirstPairing.B_act
        (geometry := replacementGeometry h d) (by omega : 2 < replacementDistance h d)
        g a p.start_color
      have hh := hi
      rw [hBi] at hh
      have hUy : (U d.radical (act d.radical y (p.walk.getVert 2))).map
          (MulAut.conj g⁻¹).toMonoidHom =
          U d.radical (act d.radical x (act d.radical g (p.walk.getVert 2))) := by
        rw [←U_act,hy,←act_mul,inv_mul_cancel,act_one]
      rw [←hUy,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective] at hh
      exact hh
    · have hh := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hgen
      rw [Subgroup.map_sup,←inv_inv g,←Q_act,←Z_act,←stabilizer_act,inv_inv,hcancel,hcancel] at hh
      simpa only [hy] using hh
  · have ht : color d.radical (beta d.radical) = false := by
      change color d.radical (hVertex d.radical 1) = false
      rw [←hg.1,action_preserves_color,p.start_color]
    cases ht


include e hz hn in
/-- Both image sizes now give a generating backward shift on the literal
replacement graph. The same element transports the first edge and second vertex. -/
theorem backwardShift_with_edge_knownSimple
    (hb : 4 < replacementDistance h d)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z) :
    ∃ q : BackwardShift (h := h) p,
      act d.radical q.transporter (p.walk.getVert 1) = q.edge := by
  by_cases hs : (Q d.radical z).relIndex (Z d.radical a) < 4
  · obtain ⟨x,hx,hat,hct,_,hgen,q,hq1,hover⟩ :=
      small_generating_step_knownSimple (e := e) (hz := hz) (hn := hn) hb p hs
    exact ⟨⟨_,_,x,hx,rfl,hat,hct,hgen,q,hq1,hover⟩,rfl⟩
  · exact EightLarge.large_backwardShift_with_edge_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p (by omega)

include e hz hn in
/-- Every path admits two generating shifts ending in a critical pair with
both images and commutator of order two. Its full first-edge kernel moves
that commutator; the choices require no critical-image premise. -/
theorem two_shifts_small_moving_knownSimple
    (hb : 4 < replacementDistance h d)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z) :
    ∃ q : BackwardShift (h := h) p, ∃ r : BackwardShift (h := h) q.path,
      act d.radical q.transporter (p.walk.getVert 1) = q.edge ∧
      act d.radical r.transporter (q.path.walk.getVert 1) = r.edge ∧
      (Q d.radical (q.path.walk.getVert (q.path.walk.length-2))).relIndex
        (Z d.radical r.start) = 2 ∧
      (Q d.radical r.start).relIndex
        (Z d.radical (q.path.walk.getVert (q.path.walk.length-2))) = 2 ∧
      Nat.card (⁅Z d.radical r.start,
        Z d.radical (q.path.walk.getVert (q.path.walk.length-2))⁆ :
        Subgroup (FreeAmalgam d.radical)) = 2 ∧
      ¬ Q d.radical (r.path.walk.getVert 1) ≤ centralizer
        ((⁅Z d.radical r.start,Z d.radical (q.path.walk.getVert (q.path.walk.length-2))⁆ :
          Subgroup (FreeAmalgam d.radical)) : Set _) := by
  obtain ⟨q,hq⟩ := backwardShift_with_edge_knownSimple (e := e) (hz := hz) (hn := hn) hb p
  obtain ⟨r,hr⟩ := backwardShift_with_edge_knownSimple (e := e) (hz := hz) (hn := hn) hb q.path
  have hh := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p q r
  exact ⟨q,r,hq,hr,hh.2⟩

include e hz hn in
/-- The original MS radical retains its index two over the chosen edge kernel
in both critical-image branches. The actual shifted critical path and transporter
are retained with the generation identity. -/
theorem original_radical_generating_backward_knownSimple
    (hb : 4 < replacementDistance h d)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hfirst : p.walk.getVert 1 = beta d.radical) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    ∃ q : BackwardShift (h := h) p,
      act d.radical q.transporter (beta d.radical) = q.edge ∧
      (Q d.radical q.edge).relIndex
        (T.map (MulAut.conj q.transporter⁻¹).toMonoidHom) = 2 := by
  obtain ⟨q,hqe⟩ := backwardShift_with_edge_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p
  rw [hfirst] at hqe
  refine ⟨q,hqe,?_⟩
  rw [←hqe,Q_act,relIndex_map_map_of_injective _ _ (MulAut.conj q.transporter⁻¹).injective,
    Q_beta,relIndex_map_map_of_injective _ _ (embedM_injective d.radical)]
  exact (SylowWholeCore.four_lt_original_sylow_eight_image_knownSimple
    (e := e) (hz := hz) (hn := hn) hb).2.2.1

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightGenerating
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
