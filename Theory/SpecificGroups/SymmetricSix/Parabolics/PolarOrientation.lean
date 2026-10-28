module
public import Theory.SpecificGroups.SymmetricSix.Parabolics.PolarActions

/-!
# Both orientations of the binary symplectic quadrangle

The actual point and isotropic-plane carriers are retained while a Boolean
records whether the two residue types are interchanged. This keeps both
parabolic markings available without postulating a compatible choice.
Source: Aschbacher–Smith, I.5.4 and I.5.9, pp.420–422.
-/

@[expose] public noncomputable section
namespace Theory.SpecificGroups.SymmetricSix.PolarOrientation

abbrev Point : Bool → Type := fun b => if b then BinaryLine else BinaryPoint
abbrev Line : Bool → Type := fun b => if b then BinaryPoint else BinaryLine
instance pointAction (b : Bool) : MulAction S6 (Point b) := by cases b <;> dsimp [Point] <;> infer_instance
instance lineAction (b : Bool) : MulAction S6 (Line b) := by cases b <;> dsimp [Line] <;> infer_instance
instance pointPretransitive (b : Bool) : MulAction.IsPretransitive S6 (Point b) := by
  cases b <;> dsimp [Point] <;> infer_instance
instance linePretransitive (b : Bool) : MulAction.IsPretransitive S6 (Line b) := by
  cases b <;> dsimp [Line] <;> infer_instance
instance a6PointPretransitive (b : Bool) : MulAction.IsPretransitive A6 (Point b) := by
  cases b
  · exact ⟨a6_polarPoint_transitive⟩
  · exact ⟨a6_polarLine_transitive⟩
instance a6LinePretransitive (b : Bool) : MulAction.IsPretransitive A6 (Line b) := by
  cases b
  · exact ⟨a6_polarLine_transitive⟩
  · exact ⟨a6_polarPoint_transitive⟩

def Inc : (b : Bool) → Point b → Line b → Prop
  | false,p,l => p.val∈l.val
  | true,p,l => l.val∈p.val

def Collinear : (b : Bool) → Point b → Point b → Prop
  | false,p,q => polarPointCollinear p q
  | true,p,q => polarLineCollinear p q

def pointCoord (b : Bool) : Fin 15 ≃ Point b := by
  cases b
  · exact duadPolarEquiv
  · exact synthemePolarEquiv

def lineCoord (b : Bool) : Fin 15 ≃ Line b := by
  cases b
  · exact synthemePolarEquiv
  · exact duadPolarEquiv

def basePoint (b : Bool) : Point b := pointCoord b 0
def baseLine (b : Bool) : Line b := lineCoord b 0

theorem incident_base (b : Bool) : Inc b (basePoint b) (baseLine b) := by
  cases b <;> exact (polar_incidence_equivalence 0 0).mp (by decide)

theorem incident_smul (b : Bool) (g : S6) (p : Point b) (l : Line b) :
    Inc b (g • p) (g • l) ↔ Inc b p l := by
  cases b
  · exact polar_incidence_smul_iff g p l
  · exact polar_incidence_smul_iff g l p

theorem flag_transitive (b : Bool) (p : Point b) (l : Line b) (h : Inc b p l) :
    ∃ g : S6, g • basePoint b=p ∧ g • baseLine b=l := by
  cases b
  · exact polar_flag_transitive _ _ _ _ (incident_base false) h
  · obtain ⟨g,hg,hg'⟩ := polar_flag_transitive _ _ _ _ (incident_base true) h
    exact ⟨g,hg',hg⟩

theorem a6_flag_transitive (b : Bool) (p : Point b) (l : Line b) (h : Inc b p l) :
    ∃ g : A6, g • basePoint b=p ∧ g • baseLine b=l := by
  cases b
  · exact a6_polar_flag_transitive _ _ _ _ (incident_base false) h
  · obtain ⟨g,hg,hg'⟩ := a6_polar_flag_transitive _ _ _ _ (incident_base true) h
    exact ⟨g,hg',hg⟩

theorem common_line_iff (b : Bool) (p q : Point b) :
    (∃ l, Inc b p l ∧ Inc b q l) ↔ p=q ∨ Collinear b p q := by
  cases b
  · obtain ⟨d,rfl⟩ := duadPolarEquiv.surjective p
    obtain ⟨e,rfl⟩ := duadPolarEquiv.surjective q
    change (∃ l : BinaryLine,(duadPolarEquiv d).val∈l.val ∧ (duadPolarEquiv e).val∈l.val) ↔
      duadPolarEquiv d=duadPolarEquiv e ∨ polarPointCollinear (duadPolarEquiv d) (duadPolarEquiv e)
    rw [duadPolarEquiv.injective.eq_iff,duadPolarEquiv_collinear_iff]
    constructor
    · rintro ⟨l,hl,hq⟩
      obtain ⟨s,rfl⟩ := synthemePolarEquiv.surjective l
      by_cases he : d=e
      · exact Or.inl he
      · exact Or.inr ((duad_collinear_iff_common_syntheme d e).mpr
          ⟨he,s,(polar_incidence_equivalence d s).mpr hl,(polar_incidence_equivalence e s).mpr hq⟩)
    · rintro (rfl|hc)
      · obtain ⟨g,hg⟩ := MulAction.exists_smul_eq S6 (basePoint false) (duadPolarEquiv d)
        exact ⟨g • baseLine false,by simpa only [hg,Inc] using
          (incident_smul false g (basePoint false) (baseLine false)).mpr (incident_base false),
          by simpa only [hg,Inc] using (incident_smul false g (basePoint false) (baseLine false)).mpr (incident_base false)⟩
      · obtain ⟨s,hd,he⟩ := ((duad_collinear_iff_common_syntheme d e).mp hc).2
        exact ⟨synthemePolarEquiv s,(polar_incidence_equivalence d s).mp hd,(polar_incidence_equivalence e s).mp he⟩
  · change (∃ l : BinaryPoint,l.val∈p.val ∧ l.val∈q.val) ↔ p=q ∨ polarLineCollinear p q
    constructor
    · intro hh
      by_cases hp : p=q
      · exact Or.inl hp
      · exact Or.inr ⟨hp,hh⟩
    · rintro (rfl|⟨_,h⟩)
      · obtain ⟨g,hg⟩ := MulAction.exists_smul_eq S6 (basePoint true) p
        exact ⟨g • baseLine true,by simpa only [hg,Inc] using
          (incident_smul true g (basePoint true) (baseLine true)).mpr (incident_base true),
          by simpa only [hg,Inc] using (incident_smul true g (basePoint true) (baseLine true)).mpr (incident_base true)⟩
      · exact h

theorem noncollinear_eight (b : Bool) (p : Point b) :
    Nat.card {q : Point b // q≠p ∧ ¬Collinear b p q}=8 := by
  cases b
  · exact polarPoint_noncollinear_eight p
  · exact polarLine_noncollinear_eight p

theorem a6_noncollinear_transporter (b : Bool) (p q r : Point b)
    (hq : q≠p ∧ ¬Collinear b p q) (hr : r≠p ∧ ¬Collinear b p r) :
    ∃ g : A6, g • p=p ∧ g • q=r := by
  cases b
  · exact a6_polarPoint_noncollinear_transporter p q r hq hr
  · exact a6_polarLine_noncollinear_transporter p q r hq hr

/-- Every point projects onto every line, in either orientation. -/
theorem projection (b : Bool) (p : Point b) (l : Line b) :
    ∃ q, Inc b q l ∧ (p=q ∨ Collinear b p q) := by
  by_cases hi : Inc b p l
  · exact ⟨p,hi,Or.inl rfl⟩
  cases b
  · obtain ⟨d,rfl⟩ := duadPolarEquiv.surjective p
    obtain ⟨s,rfl⟩ := synthemePolarEquiv.surjective l
    have hn : ¬incident d s := fun h=>hi ((polar_incidence_equivalence d s).mp h)
    obtain ⟨e,he,_⟩ := quadrangle_unique_collinear d s hn
    exact ⟨duadPolarEquiv e,(polar_incidence_equivalence e s).mp he.1,
      Or.inr ((duadPolarEquiv_collinear_iff d e).mpr he.2)⟩
  · obtain ⟨s,rfl⟩ := synthemePolarEquiv.surjective p
    obtain ⟨d,rfl⟩ := duadPolarEquiv.surjective l
    have hn : ¬incident d s := fun h=>hi ((polar_incidence_equivalence d s).mp h)
    obtain ⟨t,ht,_⟩ := quadrangle_unique_collinear_dual d s hn
    exact ⟨synthemePolarEquiv t,(polar_incidence_equivalence d t).mp ht.1,
      Or.inr ((synthemePolarEquiv_collinear_iff s t).mpr ht.2)⟩

/-- Two noncollinear points have exactly three common neighbors, also in the dual. -/
theorem common_three (b : Bool) (p q : Point b) (hne : p≠q) (hn : ¬Collinear b p q) :
    Nat.card {r : Point b // Collinear b p r ∧ Collinear b q r}=3 := by
  cases b
  · obtain ⟨d,rfl⟩ := duadPolarEquiv.surjective p
    obtain ⟨e,rfl⟩ := duadPolarEquiv.surjective q
    have hne' : d ≠ e := fun h => hne (congrArg duadPolarEquiv h)
    have hn' : ¬duadCollinear d e := fun h => hn ((duadPolarEquiv_collinear_iff d e).mpr h)
    have h (f : Duad) : (duadCollinear d f ∧ duadCollinear e f) ↔
        Collinear false (duadPolarEquiv d) (duadPolarEquiv f) ∧ Collinear false (duadPolarEquiv e) (duadPolarEquiv f) := by
      change _ ↔ polarPointCollinear _ _ ∧ polarPointCollinear _ _
      rw [duadPolarEquiv_collinear_iff,duadPolarEquiv_collinear_iff]
    let e' : {f : Duad // duadCollinear d f ∧ duadCollinear e f} ≃
        {r : BinaryPoint // Collinear false (duadPolarEquiv d) r ∧ Collinear false (duadPolarEquiv e) r} := duadPolarEquiv.subtypeEquiv h
    calc
      Nat.card {r : BinaryPoint // Collinear false (duadPolarEquiv d) r ∧ Collinear false (duadPolarEquiv e) r} = Nat.card {f : Duad // duadCollinear d f ∧ duadCollinear e f} := Nat.card_congr e'.symm
      _ = Fintype.card {f : Duad // duadCollinear d f ∧ duadCollinear e f} := Nat.card_eq_fintype_card
      _ = (duadCommon d e).card := by rw [Fintype.card_subtype]; simp [duadCommon]
      _ = 3 := duad_common_three hne' hn'
  · obtain ⟨s,rfl⟩ := synthemePolarEquiv.surjective p
    obtain ⟨t,rfl⟩ := synthemePolarEquiv.surjective q
    have hne' : s ≠ t := fun h => hne (congrArg synthemePolarEquiv h)
    have hn' : ¬synthemeCollinear s t := fun h => hn ((synthemePolarEquiv_collinear_iff s t).mpr h)
    have h (u : Syntheme) : (synthemeCollinear s u ∧ synthemeCollinear t u) ↔
        Collinear true (synthemePolarEquiv s) (synthemePolarEquiv u) ∧ Collinear true (synthemePolarEquiv t) (synthemePolarEquiv u) := by
      change _ ↔ polarLineCollinear _ _ ∧ polarLineCollinear _ _
      rw [synthemePolarEquiv_collinear_iff,synthemePolarEquiv_collinear_iff]
    let e' : {u : Syntheme // synthemeCollinear s u ∧ synthemeCollinear t u} ≃
        {r : BinaryLine // Collinear true (synthemePolarEquiv s) r ∧ Collinear true (synthemePolarEquiv t) r} := synthemePolarEquiv.subtypeEquiv h
    calc
      Nat.card {r : BinaryLine // Collinear true (synthemePolarEquiv s) r ∧ Collinear true (synthemePolarEquiv t) r} = Nat.card {u : Syntheme // synthemeCollinear s u ∧ synthemeCollinear t u} := Nat.card_congr e'.symm
      _ = Fintype.card {u : Syntheme // synthemeCollinear s u ∧ synthemeCollinear t u} := Nat.card_eq_fintype_card
      _ = (synthemeCommon s t).card := by rw [Fintype.card_subtype]; simp [synthemeCommon]
      _ = 3 := syntheme_common_three hne' hn'

end Theory.SpecificGroups.SymmetricSix.PolarOrientation
