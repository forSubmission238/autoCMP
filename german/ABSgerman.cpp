/******************************
  Program "ABSgerman.m" compiled by "Caching Murphi Release 5.5.0"

  Murphi Last Compiled date: "Mar  1 2022"
 ******************************/

/********************
  Parameter
 ********************/
#define MURPHI_VERSION "Caching Murphi Release 5.5.0"
#define MURPHI_DATE "Mar  1 2022"
#define PROTOCOL_NAME "ABSgerman"
#define BITS_IN_WORLD 120
#define ALIGN

/********************
  Include
 ********************/
#include "mu_prolog.hpp"

/********************
  Decl declaration
 ********************/

class mu_1_NODE: public mu__byte
{
 public:
  inline int operator=(int val) { return value(val); };
  inline int operator=(const mu_1_NODE& val){ return value(val.value());};
  inline operator int() const { return value(); };
  static const char *values[];
  friend ostream& operator<< (ostream& s, mu_1_NODE& val)
    {
      if (val.defined())
	return ( s << mu_1_NODE::values[ int(val) - 1 ] );
      else
	return ( s << "Undefined" );
    };

  mu_1_NODE (const char *name, int os): mu__byte(1, 2, 2, name, os) {};
  mu_1_NODE (void): mu__byte(1, 2, 2) {};
  mu_1_NODE (int val): mu__byte(1, 2, 2, "Parameter or function result.", 0)
    { operator=(val); };
  const char * Name() { return values[ value() -1]; };
  virtual void print()
    {
      if (defined()) cout << name << ':' << values[ value() - 1] << '\n';
      else cout << name << ":Undefined\n";
    };
  void print_statistic() {};
friend int CompareWeight(mu_1_NODE& a, mu_1_NODE& b)
{
  if (!a.defined() && b.defined())
    return -1;
  else if (a.defined() && !b.defined())
    return 1;
  else
    return 0;
}
  virtual void Permute(PermSet& Perm, int i);
  virtual void SimpleCanonicalize(PermSet& Perm);
  virtual void Canonicalize(PermSet& Perm);
  virtual void SimpleLimit(PermSet& Perm);
  virtual void ArrayLimit(PermSet& Perm);
  virtual void Limit(PermSet& Perm);
  virtual void MultisetLimit(PermSet& Perm);
};
const char *mu_1_NODE::values[] =
  { "NODE_1","NODE_2",NULL };

/*** end scalarset declaration ***/
mu_1_NODE mu_1_NODE_undefined_var;

class mu_1_OTHER: public mu__byte
{
 public:
  inline int operator=(int val) { return value(val); };
  inline int operator=(const mu_1_OTHER& val) { return value(val.value()); };
  static const char *values[];
  friend ostream& operator<< (ostream& s, mu_1_OTHER& val)
  {
    if (val.defined())
      return ( s << mu_1_OTHER::values[ int(val) - 3] );
    else return ( s << "Undefined" );
  };

  mu_1_OTHER (const char *name, int os): mu__byte(3, 3, 1, name, os) {};
  mu_1_OTHER (void): mu__byte(3, 3, 1) {};
  mu_1_OTHER (int val): mu__byte(3, 3, 1, "Parameter or function result.", 0)
  {
     operator=(val);
  };
  const char * Name() { return values[ value() -3]; };
  virtual void Permute(PermSet& Perm, int i);
  virtual void SimpleCanonicalize(PermSet& Perm);
  virtual void Canonicalize(PermSet& Perm);
  virtual void SimpleLimit(PermSet& Perm);
  virtual void ArrayLimit(PermSet& Perm);
  virtual void Limit(PermSet& Perm);
  virtual void MultisetLimit(PermSet& Perm);
  virtual void MultisetSort() {};
  void print_statistic() {};
  virtual void print()
  {
    if (defined())
      cout << name << ":" << values[ value() -3] << '\n';
    else
      cout << name << ":Undefined\n";
  };
};

const char *mu_1_OTHER::values[] = {"Other",NULL };

/*** end of enum declaration ***/
mu_1_OTHER mu_1_OTHER_undefined_var;

class mu_1_ABS_NODE: public mu__byte
{
 public:
  inline int operator=(int val) { return value(val); };
  inline int operator=(const mu_1_ABS_NODE& val) { return value(val.value()); };
  inline operator int() const { return value(); };
  static const char *values[];
  friend ostream& operator<< (ostream& s, mu_1_ABS_NODE& val)
    {
      if (val.defined())
	return ( s << mu_1_ABS_NODE::values[ val.indexvalue() ] );
      else
	return ( s << "Undefined" );
    };

  // note thate lb and ub are not used if we have byte compacted state.
  mu_1_ABS_NODE (const char *name, int os): mu__byte(0, 2, 2, name, os) {};
  mu_1_ABS_NODE (void): mu__byte(0, 2, 2) {};
  mu_1_ABS_NODE (int val): mu__byte(0, 2, 2, "Parameter or function result.", 0)
    { operator=(val); };
  int indexvalue()
  {
    if ((value() >= 1) && (value() <= 2)) return (value() - 1);
    if ((value() >= 3) && (value() <= 3)) return (value() - 1);
  return 0;
  };
  inline int unionassign(int val)
  {
    if (val >= 0 && val <= 1) return value(val+1);
    if (val >= 2 && val <= 2) return value(val+1);
  return 0;
  };
  const char * Name() { return values[ indexvalue() ]; };
friend int CompareWeight(mu_1_ABS_NODE& a, mu_1_ABS_NODE& b)
{
  if (!a.defined() && b.defined())
    return -1;
  else if (a.defined() && !b.defined())
    return 1;
  else
    return 0;
}
  virtual void Permute(PermSet& Perm, int i);
  virtual void SimpleCanonicalize(PermSet& Perm);
  virtual void Canonicalize(PermSet& Perm);
  virtual void SimpleLimit(PermSet& Perm);
  virtual void ArrayLimit(PermSet& Perm);
  virtual void Limit(PermSet& Perm);
  virtual void MultisetLimit(PermSet& Perm);
  virtual void print()
    {
      if (defined()) cout << name << ':' << values[ indexvalue() ] << '\n';
      else cout << name << ":Undefined\n";
    };
  void print_statistic() {};
};
const char *mu_1_ABS_NODE::values[] = {"NODE_1","NODE_2","Other",NULL };

/*** end union declaration ***/
mu_1_ABS_NODE mu_1_ABS_NODE_undefined_var;

class mu_1_CACHE_STATE: public mu__byte
{
 public:
  inline int operator=(int val) { return value(val); };
  inline int operator=(const mu_1_CACHE_STATE& val) { return value(val.value()); };
  static const char *values[];
  friend ostream& operator<< (ostream& s, mu_1_CACHE_STATE& val)
  {
    if (val.defined())
      return ( s << mu_1_CACHE_STATE::values[ int(val) - 4] );
    else return ( s << "Undefined" );
  };

  mu_1_CACHE_STATE (const char *name, int os): mu__byte(4, 6, 2, name, os) {};
  mu_1_CACHE_STATE (void): mu__byte(4, 6, 2) {};
  mu_1_CACHE_STATE (int val): mu__byte(4, 6, 2, "Parameter or function result.", 0)
  {
     operator=(val);
  };
  const char * Name() { return values[ value() -4]; };
  virtual void Permute(PermSet& Perm, int i);
  virtual void SimpleCanonicalize(PermSet& Perm);
  virtual void Canonicalize(PermSet& Perm);
  virtual void SimpleLimit(PermSet& Perm);
  virtual void ArrayLimit(PermSet& Perm);
  virtual void Limit(PermSet& Perm);
  virtual void MultisetLimit(PermSet& Perm);
  virtual void MultisetSort() {};
  void print_statistic() {};
  virtual void print()
  {
    if (defined())
      cout << name << ":" << values[ value() -4] << '\n';
    else
      cout << name << ":Undefined\n";
  };
};

const char *mu_1_CACHE_STATE::values[] = {"I","S","E",NULL };

/*** end of enum declaration ***/
mu_1_CACHE_STATE mu_1_CACHE_STATE_undefined_var;

class mu_1_CACHE
{
 public:
  char *name;
  char longname[BUFFER_SIZE/4];
  void set_self_2( const char *n, const char *n2, int os);
  void set_self_ar( const char *n, const char *n2, int os);
  void set_self(const char *n, int os);
  mu_1_CACHE_STATE mu_State;
  mu_1_CACHE ( const char *n, int os ) { set_self(n,os); };
  mu_1_CACHE ( void ) {};

  virtual ~mu_1_CACHE(); 
friend int CompareWeight(mu_1_CACHE& a, mu_1_CACHE& b)
  {
    int w;
    w = CompareWeight(a.mu_State, b.mu_State);
    if (w!=0) return w;
  return 0;
}
friend int Compare(mu_1_CACHE& a, mu_1_CACHE& b)
  {
    int w;
    w = Compare(a.mu_State, b.mu_State);
    if (w!=0) return w;
  return 0;
}
  virtual void Permute(PermSet& Perm, int i);
  virtual void SimpleCanonicalize(PermSet& Perm);
  virtual void Canonicalize(PermSet& Perm);
  virtual void SimpleLimit(PermSet& Perm);
  virtual void ArrayLimit(PermSet& Perm);
  virtual void Limit(PermSet& Perm);
  virtual void MultisetLimit(PermSet& Perm);
  virtual void MultisetSort()
  {
    mu_State.MultisetSort();
  }
  void print_statistic()
  {
    mu_State.print_statistic();
  }
  void clear() {
    mu_State.clear();
 };
  void undefine() {
    mu_State.undefine();
 };
  void reset() {
    mu_State.reset();
 };
  void print() {
    mu_State.print();
  };
  void print_diff(state *prevstate) {
    mu_State.print_diff(prevstate);
  };
  void to_state(state *thestate) {
    mu_State.to_state(thestate);
  };
virtual bool isundefined() { Error.Error("Checking undefinedness of a non-base type"); return TRUE;}
virtual bool ismember() { Error.Error("Checking membership for a non-base type"); return TRUE;}
  mu_1_CACHE& operator= (const mu_1_CACHE& from) {
    mu_State.value(from.mu_State.value());
    return *this;
  };
};

  void mu_1_CACHE::set_self_ar( const char *n1, const char *n2, int os ) {
    if (n1 == NULL) {set_self(NULL, 0); return;}
    int l1 = strlen(n1), l2 = strlen(n2);
    strcpy( longname, n1 );
    longname[l1] = '[';
    strcpy( longname+l1+1, n2 );
    longname[l1+l2+1] = ']';
    longname[l1+l2+2] = 0;
    set_self( longname, os );
  };
  void mu_1_CACHE::set_self_2( const char *n1, const char *n2, int os ) {
    if (n1 == NULL) {set_self(NULL, 0); return;}
    strcpy( longname, n1 );
    strcat( longname, n2 );
    set_self( longname, os );
  };
void mu_1_CACHE::set_self(const char *n, int os)
{
  name = (char *)n;

  if (name) mu_State.set_self_2(name, ".State", os + 0 ); else mu_State.set_self_2(NULL, NULL, 0);
}

mu_1_CACHE::~mu_1_CACHE()
{
}

/*** end record declaration ***/
mu_1_CACHE mu_1_CACHE_undefined_var;

class mu_1_MSG_CMD: public mu__byte
{
 public:
  inline int operator=(int val) { return value(val); };
  inline int operator=(const mu_1_MSG_CMD& val) { return value(val.value()); };
  static const char *values[];
  friend ostream& operator<< (ostream& s, mu_1_MSG_CMD& val)
  {
    if (val.defined())
      return ( s << mu_1_MSG_CMD::values[ int(val) - 7] );
    else return ( s << "Undefined" );
  };

  mu_1_MSG_CMD (const char *name, int os): mu__byte(7, 13, 3, name, os) {};
  mu_1_MSG_CMD (void): mu__byte(7, 13, 3) {};
  mu_1_MSG_CMD (int val): mu__byte(7, 13, 3, "Parameter or function result.", 0)
  {
     operator=(val);
  };
  const char * Name() { return values[ value() -7]; };
  virtual void Permute(PermSet& Perm, int i);
  virtual void SimpleCanonicalize(PermSet& Perm);
  virtual void Canonicalize(PermSet& Perm);
  virtual void SimpleLimit(PermSet& Perm);
  virtual void ArrayLimit(PermSet& Perm);
  virtual void Limit(PermSet& Perm);
  virtual void MultisetLimit(PermSet& Perm);
  virtual void MultisetSort() {};
  void print_statistic() {};
  virtual void print()
  {
    if (defined())
      cout << name << ":" << values[ value() -7] << '\n';
    else
      cout << name << ":Undefined\n";
  };
};

const char *mu_1_MSG_CMD::values[] = {"Empty","ReqS","ReqE","Inv","InvAck","GntS","GntE",NULL };

/*** end of enum declaration ***/
mu_1_MSG_CMD mu_1_MSG_CMD_undefined_var;

class mu_1_MSG
{
 public:
  char *name;
  char longname[BUFFER_SIZE/4];
  void set_self_2( const char *n, const char *n2, int os);
  void set_self_ar( const char *n, const char *n2, int os);
  void set_self(const char *n, int os);
  mu_1_MSG_CMD mu_Cmd;
  mu_1_MSG ( const char *n, int os ) { set_self(n,os); };
  mu_1_MSG ( void ) {};

  virtual ~mu_1_MSG(); 
friend int CompareWeight(mu_1_MSG& a, mu_1_MSG& b)
  {
    int w;
    w = CompareWeight(a.mu_Cmd, b.mu_Cmd);
    if (w!=0) return w;
  return 0;
}
friend int Compare(mu_1_MSG& a, mu_1_MSG& b)
  {
    int w;
    w = Compare(a.mu_Cmd, b.mu_Cmd);
    if (w!=0) return w;
  return 0;
}
  virtual void Permute(PermSet& Perm, int i);
  virtual void SimpleCanonicalize(PermSet& Perm);
  virtual void Canonicalize(PermSet& Perm);
  virtual void SimpleLimit(PermSet& Perm);
  virtual void ArrayLimit(PermSet& Perm);
  virtual void Limit(PermSet& Perm);
  virtual void MultisetLimit(PermSet& Perm);
  virtual void MultisetSort()
  {
    mu_Cmd.MultisetSort();
  }
  void print_statistic()
  {
    mu_Cmd.print_statistic();
  }
  void clear() {
    mu_Cmd.clear();
 };
  void undefine() {
    mu_Cmd.undefine();
 };
  void reset() {
    mu_Cmd.reset();
 };
  void print() {
    mu_Cmd.print();
  };
  void print_diff(state *prevstate) {
    mu_Cmd.print_diff(prevstate);
  };
  void to_state(state *thestate) {
    mu_Cmd.to_state(thestate);
  };
virtual bool isundefined() { Error.Error("Checking undefinedness of a non-base type"); return TRUE;}
virtual bool ismember() { Error.Error("Checking membership for a non-base type"); return TRUE;}
  mu_1_MSG& operator= (const mu_1_MSG& from) {
    mu_Cmd.value(from.mu_Cmd.value());
    return *this;
  };
};

  void mu_1_MSG::set_self_ar( const char *n1, const char *n2, int os ) {
    if (n1 == NULL) {set_self(NULL, 0); return;}
    int l1 = strlen(n1), l2 = strlen(n2);
    strcpy( longname, n1 );
    longname[l1] = '[';
    strcpy( longname+l1+1, n2 );
    longname[l1+l2+1] = ']';
    longname[l1+l2+2] = 0;
    set_self( longname, os );
  };
  void mu_1_MSG::set_self_2( const char *n1, const char *n2, int os ) {
    if (n1 == NULL) {set_self(NULL, 0); return;}
    strcpy( longname, n1 );
    strcat( longname, n2 );
    set_self( longname, os );
  };
void mu_1_MSG::set_self(const char *n, int os)
{
  name = (char *)n;

  if (name) mu_Cmd.set_self_2(name, ".Cmd", os + 0 ); else mu_Cmd.set_self_2(NULL, NULL, 0);
}

mu_1_MSG::~mu_1_MSG()
{
}

/*** end record declaration ***/
mu_1_MSG mu_1_MSG_undefined_var;

class mu_1__type_0
{
 public:
  mu_1_CACHE array[ 2 ];
 public:
  char *name;
  char longname[BUFFER_SIZE/4];
  void set_self( const char *n, int os);
  void set_self_2( const char *n, const char *n2, int os);
  void set_self_ar( const char *n, const char *n2, int os);
  mu_1__type_0 (const char *n, int os) { set_self(n, os); };
  mu_1__type_0 ( void ) {};
  virtual ~mu_1__type_0 ();
  mu_1_CACHE& operator[] (int index) /* const */
  {
#ifndef NO_RUN_TIME_CHECKING
    if ( ( index >= 1 ) && ( index <= 2 ) )
      return array[ index - 1 ];
    else
      {
	if (index==UNDEFVAL) 
	  Error.Error("Indexing to %s using an undefined value.", name);
	else
	  Error.Error("Funny index value %d for %s: NODE is internally represented from 1 to 2.\nInternal Error in Type checking.",index, name);
	return array[0];
      }
#else
    return array[ index - 1 ];
#endif
  };
  mu_1__type_0& operator= (const mu_1__type_0& from)
  {
    for (int i = 0; i < 2; i++)
      array[i] = from.array[i];
    return *this;
  }

friend int CompareWeight(mu_1__type_0& a, mu_1__type_0& b)
  {
    return 0;
  }
friend int Compare(mu_1__type_0& a, mu_1__type_0& b)
  {
    int w;
    for (int i=0; i<2; i++) {
      w = Compare(a.array[i], b.array[i]);
      if (w!=0) return w;
    }
    return 0;
  }
  virtual void Permute(PermSet& Perm, int i);
  virtual void SimpleCanonicalize(PermSet& Perm);
  virtual void Canonicalize(PermSet& Perm);
  virtual void SimpleLimit(PermSet& Perm);
  virtual void ArrayLimit(PermSet& Perm);
  virtual void Limit(PermSet& Perm);
  virtual void MultisetLimit(PermSet& Perm);
  virtual void MultisetSort()
  {
    for (int i=0; i<2; i++)
      array[i].MultisetSort();
  }
  void print_statistic()
  {
    for (int i=0; i<2; i++)
      array[i].print_statistic();
  }
  void clear() { for (int i = 0; i < 2; i++) array[i].clear(); };

  void undefine() { for (int i = 0; i < 2; i++) array[i].undefine(); };

  void reset() { for (int i = 0; i < 2; i++) array[i].reset(); };

  void to_state(state *thestate)
  {
    for (int i = 0; i < 2; i++)
      array[i].to_state(thestate);
  };

  void print()
  {
    for (int i = 0; i < 2; i++)
      array[i].print(); };

  void print_diff(state *prevstate)
  {
    for (int i = 0; i < 2; i++)
      array[i].print_diff(prevstate);
  };
};

  void mu_1__type_0::set_self_ar( const char *n1, const char *n2, int os ) {
    if (n1 == NULL) {set_self(NULL, 0); return;}
    int l1 = strlen(n1), l2 = strlen(n2);
    strcpy( longname, n1 );
    longname[l1] = '[';
    strcpy( longname+l1+1, n2 );
    longname[l1+l2+1] = ']';
    longname[l1+l2+2] = 0;
    set_self( longname, os );
  };
  void mu_1__type_0::set_self_2( const char *n1, const char *n2, int os ) {
    if (n1 == NULL) {set_self(NULL, 0); return;}
    strcpy( longname, n1 );
    strcat( longname, n2 );
    set_self( longname, os );
  };
void mu_1__type_0::set_self( const char *n, int os)
  {
    int i=0;
    name = (char *)n;

if (n) array[i].set_self_ar(n,"NODE_1", i * 8 + os); else array[i].set_self_ar(NULL, NULL, 0); i++;
if (n) array[i].set_self_ar(n,"NODE_2", i * 8 + os); else array[i].set_self_ar(NULL, NULL, 0); i++;
}
mu_1__type_0::~mu_1__type_0()
{
}
/*** end array declaration ***/
mu_1__type_0 mu_1__type_0_undefined_var;

class mu_1__type_1
{
 public:
  mu_1_MSG array[ 2 ];
 public:
  char *name;
  char longname[BUFFER_SIZE/4];
  void set_self( const char *n, int os);
  void set_self_2( const char *n, const char *n2, int os);
  void set_self_ar( const char *n, const char *n2, int os);
  mu_1__type_1 (const char *n, int os) { set_self(n, os); };
  mu_1__type_1 ( void ) {};
  virtual ~mu_1__type_1 ();
  mu_1_MSG& operator[] (int index) /* const */
  {
#ifndef NO_RUN_TIME_CHECKING
    if ( ( index >= 1 ) && ( index <= 2 ) )
      return array[ index - 1 ];
    else
      {
	if (index==UNDEFVAL) 
	  Error.Error("Indexing to %s using an undefined value.", name);
	else
	  Error.Error("Funny index value %d for %s: NODE is internally represented from 1 to 2.\nInternal Error in Type checking.",index, name);
	return array[0];
      }
#else
    return array[ index - 1 ];
#endif
  };
  mu_1__type_1& operator= (const mu_1__type_1& from)
  {
    for (int i = 0; i < 2; i++)
      array[i] = from.array[i];
    return *this;
  }

friend int CompareWeight(mu_1__type_1& a, mu_1__type_1& b)
  {
    return 0;
  }
friend int Compare(mu_1__type_1& a, mu_1__type_1& b)
  {
    int w;
    for (int i=0; i<2; i++) {
      w = Compare(a.array[i], b.array[i]);
      if (w!=0) return w;
    }
    return 0;
  }
  virtual void Permute(PermSet& Perm, int i);
  virtual void SimpleCanonicalize(PermSet& Perm);
  virtual void Canonicalize(PermSet& Perm);
  virtual void SimpleLimit(PermSet& Perm);
  virtual void ArrayLimit(PermSet& Perm);
  virtual void Limit(PermSet& Perm);
  virtual void MultisetLimit(PermSet& Perm);
  virtual void MultisetSort()
  {
    for (int i=0; i<2; i++)
      array[i].MultisetSort();
  }
  void print_statistic()
  {
    for (int i=0; i<2; i++)
      array[i].print_statistic();
  }
  void clear() { for (int i = 0; i < 2; i++) array[i].clear(); };

  void undefine() { for (int i = 0; i < 2; i++) array[i].undefine(); };

  void reset() { for (int i = 0; i < 2; i++) array[i].reset(); };

  void to_state(state *thestate)
  {
    for (int i = 0; i < 2; i++)
      array[i].to_state(thestate);
  };

  void print()
  {
    for (int i = 0; i < 2; i++)
      array[i].print(); };

  void print_diff(state *prevstate)
  {
    for (int i = 0; i < 2; i++)
      array[i].print_diff(prevstate);
  };
};

  void mu_1__type_1::set_self_ar( const char *n1, const char *n2, int os ) {
    if (n1 == NULL) {set_self(NULL, 0); return;}
    int l1 = strlen(n1), l2 = strlen(n2);
    strcpy( longname, n1 );
    longname[l1] = '[';
    strcpy( longname+l1+1, n2 );
    longname[l1+l2+1] = ']';
    longname[l1+l2+2] = 0;
    set_self( longname, os );
  };
  void mu_1__type_1::set_self_2( const char *n1, const char *n2, int os ) {
    if (n1 == NULL) {set_self(NULL, 0); return;}
    strcpy( longname, n1 );
    strcat( longname, n2 );
    set_self( longname, os );
  };
void mu_1__type_1::set_self( const char *n, int os)
  {
    int i=0;
    name = (char *)n;

if (n) array[i].set_self_ar(n,"NODE_1", i * 8 + os); else array[i].set_self_ar(NULL, NULL, 0); i++;
if (n) array[i].set_self_ar(n,"NODE_2", i * 8 + os); else array[i].set_self_ar(NULL, NULL, 0); i++;
}
mu_1__type_1::~mu_1__type_1()
{
}
/*** end array declaration ***/
mu_1__type_1 mu_1__type_1_undefined_var;

class mu_1__type_2
{
 public:
  mu_1_MSG array[ 2 ];
 public:
  char *name;
  char longname[BUFFER_SIZE/4];
  void set_self( const char *n, int os);
  void set_self_2( const char *n, const char *n2, int os);
  void set_self_ar( const char *n, const char *n2, int os);
  mu_1__type_2 (const char *n, int os) { set_self(n, os); };
  mu_1__type_2 ( void ) {};
  virtual ~mu_1__type_2 ();
  mu_1_MSG& operator[] (int index) /* const */
  {
#ifndef NO_RUN_TIME_CHECKING
    if ( ( index >= 1 ) && ( index <= 2 ) )
      return array[ index - 1 ];
    else
      {
	if (index==UNDEFVAL) 
	  Error.Error("Indexing to %s using an undefined value.", name);
	else
	  Error.Error("Funny index value %d for %s: NODE is internally represented from 1 to 2.\nInternal Error in Type checking.",index, name);
	return array[0];
      }
#else
    return array[ index - 1 ];
#endif
  };
  mu_1__type_2& operator= (const mu_1__type_2& from)
  {
    for (int i = 0; i < 2; i++)
      array[i] = from.array[i];
    return *this;
  }

friend int CompareWeight(mu_1__type_2& a, mu_1__type_2& b)
  {
    return 0;
  }
friend int Compare(mu_1__type_2& a, mu_1__type_2& b)
  {
    int w;
    for (int i=0; i<2; i++) {
      w = Compare(a.array[i], b.array[i]);
      if (w!=0) return w;
    }
    return 0;
  }
  virtual void Permute(PermSet& Perm, int i);
  virtual void SimpleCanonicalize(PermSet& Perm);
  virtual void Canonicalize(PermSet& Perm);
  virtual void SimpleLimit(PermSet& Perm);
  virtual void ArrayLimit(PermSet& Perm);
  virtual void Limit(PermSet& Perm);
  virtual void MultisetLimit(PermSet& Perm);
  virtual void MultisetSort()
  {
    for (int i=0; i<2; i++)
      array[i].MultisetSort();
  }
  void print_statistic()
  {
    for (int i=0; i<2; i++)
      array[i].print_statistic();
  }
  void clear() { for (int i = 0; i < 2; i++) array[i].clear(); };

  void undefine() { for (int i = 0; i < 2; i++) array[i].undefine(); };

  void reset() { for (int i = 0; i < 2; i++) array[i].reset(); };

  void to_state(state *thestate)
  {
    for (int i = 0; i < 2; i++)
      array[i].to_state(thestate);
  };

  void print()
  {
    for (int i = 0; i < 2; i++)
      array[i].print(); };

  void print_diff(state *prevstate)
  {
    for (int i = 0; i < 2; i++)
      array[i].print_diff(prevstate);
  };
};

  void mu_1__type_2::set_self_ar( const char *n1, const char *n2, int os ) {
    if (n1 == NULL) {set_self(NULL, 0); return;}
    int l1 = strlen(n1), l2 = strlen(n2);
    strcpy( longname, n1 );
    longname[l1] = '[';
    strcpy( longname+l1+1, n2 );
    longname[l1+l2+1] = ']';
    longname[l1+l2+2] = 0;
    set_self( longname, os );
  };
  void mu_1__type_2::set_self_2( const char *n1, const char *n2, int os ) {
    if (n1 == NULL) {set_self(NULL, 0); return;}
    strcpy( longname, n1 );
    strcat( longname, n2 );
    set_self( longname, os );
  };
void mu_1__type_2::set_self( const char *n, int os)
  {
    int i=0;
    name = (char *)n;

if (n) array[i].set_self_ar(n,"NODE_1", i * 8 + os); else array[i].set_self_ar(NULL, NULL, 0); i++;
if (n) array[i].set_self_ar(n,"NODE_2", i * 8 + os); else array[i].set_self_ar(NULL, NULL, 0); i++;
}
mu_1__type_2::~mu_1__type_2()
{
}
/*** end array declaration ***/
mu_1__type_2 mu_1__type_2_undefined_var;

class mu_1__type_3
{
 public:
  mu_1_MSG array[ 2 ];
 public:
  char *name;
  char longname[BUFFER_SIZE/4];
  void set_self( const char *n, int os);
  void set_self_2( const char *n, const char *n2, int os);
  void set_self_ar( const char *n, const char *n2, int os);
  mu_1__type_3 (const char *n, int os) { set_self(n, os); };
  mu_1__type_3 ( void ) {};
  virtual ~mu_1__type_3 ();
  mu_1_MSG& operator[] (int index) /* const */
  {
#ifndef NO_RUN_TIME_CHECKING
    if ( ( index >= 1 ) && ( index <= 2 ) )
      return array[ index - 1 ];
    else
      {
	if (index==UNDEFVAL) 
	  Error.Error("Indexing to %s using an undefined value.", name);
	else
	  Error.Error("Funny index value %d for %s: NODE is internally represented from 1 to 2.\nInternal Error in Type checking.",index, name);
	return array[0];
      }
#else
    return array[ index - 1 ];
#endif
  };
  mu_1__type_3& operator= (const mu_1__type_3& from)
  {
    for (int i = 0; i < 2; i++)
      array[i] = from.array[i];
    return *this;
  }

friend int CompareWeight(mu_1__type_3& a, mu_1__type_3& b)
  {
    return 0;
  }
friend int Compare(mu_1__type_3& a, mu_1__type_3& b)
  {
    int w;
    for (int i=0; i<2; i++) {
      w = Compare(a.array[i], b.array[i]);
      if (w!=0) return w;
    }
    return 0;
  }
  virtual void Permute(PermSet& Perm, int i);
  virtual void SimpleCanonicalize(PermSet& Perm);
  virtual void Canonicalize(PermSet& Perm);
  virtual void SimpleLimit(PermSet& Perm);
  virtual void ArrayLimit(PermSet& Perm);
  virtual void Limit(PermSet& Perm);
  virtual void MultisetLimit(PermSet& Perm);
  virtual void MultisetSort()
  {
    for (int i=0; i<2; i++)
      array[i].MultisetSort();
  }
  void print_statistic()
  {
    for (int i=0; i<2; i++)
      array[i].print_statistic();
  }
  void clear() { for (int i = 0; i < 2; i++) array[i].clear(); };

  void undefine() { for (int i = 0; i < 2; i++) array[i].undefine(); };

  void reset() { for (int i = 0; i < 2; i++) array[i].reset(); };

  void to_state(state *thestate)
  {
    for (int i = 0; i < 2; i++)
      array[i].to_state(thestate);
  };

  void print()
  {
    for (int i = 0; i < 2; i++)
      array[i].print(); };

  void print_diff(state *prevstate)
  {
    for (int i = 0; i < 2; i++)
      array[i].print_diff(prevstate);
  };
};

  void mu_1__type_3::set_self_ar( const char *n1, const char *n2, int os ) {
    if (n1 == NULL) {set_self(NULL, 0); return;}
    int l1 = strlen(n1), l2 = strlen(n2);
    strcpy( longname, n1 );
    longname[l1] = '[';
    strcpy( longname+l1+1, n2 );
    longname[l1+l2+1] = ']';
    longname[l1+l2+2] = 0;
    set_self( longname, os );
  };
  void mu_1__type_3::set_self_2( const char *n1, const char *n2, int os ) {
    if (n1 == NULL) {set_self(NULL, 0); return;}
    strcpy( longname, n1 );
    strcat( longname, n2 );
    set_self( longname, os );
  };
void mu_1__type_3::set_self( const char *n, int os)
  {
    int i=0;
    name = (char *)n;

if (n) array[i].set_self_ar(n,"NODE_1", i * 8 + os); else array[i].set_self_ar(NULL, NULL, 0); i++;
if (n) array[i].set_self_ar(n,"NODE_2", i * 8 + os); else array[i].set_self_ar(NULL, NULL, 0); i++;
}
mu_1__type_3::~mu_1__type_3()
{
}
/*** end array declaration ***/
mu_1__type_3 mu_1__type_3_undefined_var;

class mu_1__type_4
{
 public:
  mu_0_boolean array[ 2 ];
 public:
  char *name;
  char longname[BUFFER_SIZE/4];
  void set_self( const char *n, int os);
  void set_self_2( const char *n, const char *n2, int os);
  void set_self_ar( const char *n, const char *n2, int os);
  mu_1__type_4 (const char *n, int os) { set_self(n, os); };
  mu_1__type_4 ( void ) {};
  virtual ~mu_1__type_4 ();
  mu_0_boolean& operator[] (int index) /* const */
  {
#ifndef NO_RUN_TIME_CHECKING
    if ( ( index >= 1 ) && ( index <= 2 ) )
      return array[ index - 1 ];
    else
      {
	if (index==UNDEFVAL) 
	  Error.Error("Indexing to %s using an undefined value.", name);
	else
	  Error.Error("Funny index value %d for %s: NODE is internally represented from 1 to 2.\nInternal Error in Type checking.",index, name);
	return array[0];
      }
#else
    return array[ index - 1 ];
#endif
  };
  mu_1__type_4& operator= (const mu_1__type_4& from)
  {
    for (int i = 0; i < 2; i++)
      array[i].value(from.array[i].value());
    return *this;
  }

friend int CompareWeight(mu_1__type_4& a, mu_1__type_4& b)
  {
    return 0;
  }
friend int Compare(mu_1__type_4& a, mu_1__type_4& b)
  {
    int w;
    for (int i=0; i<2; i++) {
      w = Compare(a.array[i], b.array[i]);
      if (w!=0) return w;
    }
    return 0;
  }
  virtual void Permute(PermSet& Perm, int i);
  virtual void SimpleCanonicalize(PermSet& Perm);
  virtual void Canonicalize(PermSet& Perm);
  virtual void SimpleLimit(PermSet& Perm);
  virtual void ArrayLimit(PermSet& Perm);
  virtual void Limit(PermSet& Perm);
  virtual void MultisetLimit(PermSet& Perm);
  virtual void MultisetSort()
  {
    for (int i=0; i<2; i++)
      array[i].MultisetSort();
  }
  void print_statistic()
  {
    for (int i=0; i<2; i++)
      array[i].print_statistic();
  }
  void clear() { for (int i = 0; i < 2; i++) array[i].clear(); };

  void undefine() { for (int i = 0; i < 2; i++) array[i].undefine(); };

  void reset() { for (int i = 0; i < 2; i++) array[i].reset(); };

  void to_state(state *thestate)
  {
    for (int i = 0; i < 2; i++)
      array[i].to_state(thestate);
  };

  void print()
  {
    for (int i = 0; i < 2; i++)
      array[i].print(); };

  void print_diff(state *prevstate)
  {
    for (int i = 0; i < 2; i++)
      array[i].print_diff(prevstate);
  };
};

  void mu_1__type_4::set_self_ar( const char *n1, const char *n2, int os ) {
    if (n1 == NULL) {set_self(NULL, 0); return;}
    int l1 = strlen(n1), l2 = strlen(n2);
    strcpy( longname, n1 );
    longname[l1] = '[';
    strcpy( longname+l1+1, n2 );
    longname[l1+l2+1] = ']';
    longname[l1+l2+2] = 0;
    set_self( longname, os );
  };
  void mu_1__type_4::set_self_2( const char *n1, const char *n2, int os ) {
    if (n1 == NULL) {set_self(NULL, 0); return;}
    strcpy( longname, n1 );
    strcat( longname, n2 );
    set_self( longname, os );
  };
void mu_1__type_4::set_self( const char *n, int os)
  {
    int i=0;
    name = (char *)n;

if (n) array[i].set_self_ar(n,"NODE_1", i * 8 + os); else array[i].set_self_ar(NULL, NULL, 0); i++;
if (n) array[i].set_self_ar(n,"NODE_2", i * 8 + os); else array[i].set_self_ar(NULL, NULL, 0); i++;
}
mu_1__type_4::~mu_1__type_4()
{
}
/*** end array declaration ***/
mu_1__type_4 mu_1__type_4_undefined_var;

class mu_1__type_5
{
 public:
  mu_0_boolean array[ 2 ];
 public:
  char *name;
  char longname[BUFFER_SIZE/4];
  void set_self( const char *n, int os);
  void set_self_2( const char *n, const char *n2, int os);
  void set_self_ar( const char *n, const char *n2, int os);
  mu_1__type_5 (const char *n, int os) { set_self(n, os); };
  mu_1__type_5 ( void ) {};
  virtual ~mu_1__type_5 ();
  mu_0_boolean& operator[] (int index) /* const */
  {
#ifndef NO_RUN_TIME_CHECKING
    if ( ( index >= 1 ) && ( index <= 2 ) )
      return array[ index - 1 ];
    else
      {
	if (index==UNDEFVAL) 
	  Error.Error("Indexing to %s using an undefined value.", name);
	else
	  Error.Error("Funny index value %d for %s: NODE is internally represented from 1 to 2.\nInternal Error in Type checking.",index, name);
	return array[0];
      }
#else
    return array[ index - 1 ];
#endif
  };
  mu_1__type_5& operator= (const mu_1__type_5& from)
  {
    for (int i = 0; i < 2; i++)
      array[i].value(from.array[i].value());
    return *this;
  }

friend int CompareWeight(mu_1__type_5& a, mu_1__type_5& b)
  {
    return 0;
  }
friend int Compare(mu_1__type_5& a, mu_1__type_5& b)
  {
    int w;
    for (int i=0; i<2; i++) {
      w = Compare(a.array[i], b.array[i]);
      if (w!=0) return w;
    }
    return 0;
  }
  virtual void Permute(PermSet& Perm, int i);
  virtual void SimpleCanonicalize(PermSet& Perm);
  virtual void Canonicalize(PermSet& Perm);
  virtual void SimpleLimit(PermSet& Perm);
  virtual void ArrayLimit(PermSet& Perm);
  virtual void Limit(PermSet& Perm);
  virtual void MultisetLimit(PermSet& Perm);
  virtual void MultisetSort()
  {
    for (int i=0; i<2; i++)
      array[i].MultisetSort();
  }
  void print_statistic()
  {
    for (int i=0; i<2; i++)
      array[i].print_statistic();
  }
  void clear() { for (int i = 0; i < 2; i++) array[i].clear(); };

  void undefine() { for (int i = 0; i < 2; i++) array[i].undefine(); };

  void reset() { for (int i = 0; i < 2; i++) array[i].reset(); };

  void to_state(state *thestate)
  {
    for (int i = 0; i < 2; i++)
      array[i].to_state(thestate);
  };

  void print()
  {
    for (int i = 0; i < 2; i++)
      array[i].print(); };

  void print_diff(state *prevstate)
  {
    for (int i = 0; i < 2; i++)
      array[i].print_diff(prevstate);
  };
};

  void mu_1__type_5::set_self_ar( const char *n1, const char *n2, int os ) {
    if (n1 == NULL) {set_self(NULL, 0); return;}
    int l1 = strlen(n1), l2 = strlen(n2);
    strcpy( longname, n1 );
    longname[l1] = '[';
    strcpy( longname+l1+1, n2 );
    longname[l1+l2+1] = ']';
    longname[l1+l2+2] = 0;
    set_self( longname, os );
  };
  void mu_1__type_5::set_self_2( const char *n1, const char *n2, int os ) {
    if (n1 == NULL) {set_self(NULL, 0); return;}
    strcpy( longname, n1 );
    strcat( longname, n2 );
    set_self( longname, os );
  };
void mu_1__type_5::set_self( const char *n, int os)
  {
    int i=0;
    name = (char *)n;

if (n) array[i].set_self_ar(n,"NODE_1", i * 8 + os); else array[i].set_self_ar(NULL, NULL, 0); i++;
if (n) array[i].set_self_ar(n,"NODE_2", i * 8 + os); else array[i].set_self_ar(NULL, NULL, 0); i++;
}
mu_1__type_5::~mu_1__type_5()
{
}
/*** end array declaration ***/
mu_1__type_5 mu_1__type_5_undefined_var;

const int mu_NODE_NUM = 2;
const int mu_NODE_1 = 1;
const int mu_NODE_2 = 2;
const int mu_Other = 3;
const int mu_I = 4;
const int mu_S = 5;
const int mu_E = 6;
const int mu_Empty = 7;
const int mu_ReqS = 8;
const int mu_ReqE = 9;
const int mu_Inv = 10;
const int mu_InvAck = 11;
const int mu_GntS = 12;
const int mu_GntE = 13;
/*** Variable declaration ***/
mu_1__type_0 mu_Cache("Cache",0);

/*** Variable declaration ***/
mu_1__type_1 mu_Chan1("Chan1",16);

/*** Variable declaration ***/
mu_1__type_2 mu_Chan2("Chan2",32);

/*** Variable declaration ***/
mu_1__type_3 mu_Chan3("Chan3",48);

/*** Variable declaration ***/
mu_1__type_4 mu_InvSet("InvSet",64);

/*** Variable declaration ***/
mu_1__type_5 mu_ShrSet("ShrSet",80);

/*** Variable declaration ***/
mu_0_boolean mu_ExGntd("ExGntd",96);

/*** Variable declaration ***/
mu_1_MSG_CMD mu_CurCmd("CurCmd",104);

/*** Variable declaration ***/
mu_1_ABS_NODE mu_CurPtr("CurPtr",112);





/********************
  The world
 ********************/
void world_class::clear()
{
  mu_Cache.clear();
  mu_Chan1.clear();
  mu_Chan2.clear();
  mu_Chan3.clear();
  mu_InvSet.clear();
  mu_ShrSet.clear();
  mu_ExGntd.clear();
  mu_CurCmd.clear();
  mu_CurPtr.clear();
}
void world_class::undefine()
{
  mu_Cache.undefine();
  mu_Chan1.undefine();
  mu_Chan2.undefine();
  mu_Chan3.undefine();
  mu_InvSet.undefine();
  mu_ShrSet.undefine();
  mu_ExGntd.undefine();
  mu_CurCmd.undefine();
  mu_CurPtr.undefine();
}
void world_class::reset()
{
  mu_Cache.reset();
  mu_Chan1.reset();
  mu_Chan2.reset();
  mu_Chan3.reset();
  mu_InvSet.reset();
  mu_ShrSet.reset();
  mu_ExGntd.reset();
  mu_CurCmd.reset();
  mu_CurPtr.reset();
}
void world_class::print()
{
  static int num_calls = 0; /* to ward off recursive calls. */
  if ( num_calls == 0 ) {
    num_calls++;
  mu_Cache.print();
  mu_Chan1.print();
  mu_Chan2.print();
  mu_Chan3.print();
  mu_InvSet.print();
  mu_ShrSet.print();
  mu_ExGntd.print();
  mu_CurCmd.print();
  mu_CurPtr.print();
    num_calls--;
}
}
void world_class::print_statistic()
{
  static int num_calls = 0; /* to ward off recursive calls. */
  if ( num_calls == 0 ) {
    num_calls++;
  mu_Cache.print_statistic();
  mu_Chan1.print_statistic();
  mu_Chan2.print_statistic();
  mu_Chan3.print_statistic();
  mu_InvSet.print_statistic();
  mu_ShrSet.print_statistic();
  mu_ExGntd.print_statistic();
  mu_CurCmd.print_statistic();
  mu_CurPtr.print_statistic();
    num_calls--;
}
}
void world_class::print_diff( state *prevstate )
{
  if ( prevstate != NULL )
  {
    mu_Cache.print_diff(prevstate);
    mu_Chan1.print_diff(prevstate);
    mu_Chan2.print_diff(prevstate);
    mu_Chan3.print_diff(prevstate);
    mu_InvSet.print_diff(prevstate);
    mu_ShrSet.print_diff(prevstate);
    mu_ExGntd.print_diff(prevstate);
    mu_CurCmd.print_diff(prevstate);
    mu_CurPtr.print_diff(prevstate);
  }
  else
print();
}
void world_class::to_state(state *newstate)
{
  mu_Cache.to_state( newstate );
  mu_Chan1.to_state( newstate );
  mu_Chan2.to_state( newstate );
  mu_Chan3.to_state( newstate );
  mu_InvSet.to_state( newstate );
  mu_ShrSet.to_state( newstate );
  mu_ExGntd.to_state( newstate );
  mu_CurCmd.to_state( newstate );
  mu_CurPtr.to_state( newstate );
}
void world_class::setstate(state *thestate)
{
}


/********************
  Rule declarations
 ********************/
/******************** RuleBase0 ********************/
class RuleBase0
{
public:
  int Priority()
  {
    return 0;
  }
  char * Name(unsigned r)
  {
    return tsprintf("ABS_RecvInvAck1");
  }
  bool Condition(unsigned r)
  {
bool mu__boolexpr6;
bool mu__boolexpr7;
  if (!((mu_CurCmd) != (mu_Empty))) mu__boolexpr7 = FALSE ;
  else {
  mu__boolexpr7 = ((mu_ExGntd) == (mu_true)) ; 
}
  if (!(mu__boolexpr7)) mu__boolexpr6 = FALSE ;
  else {
bool mu__quant8; 
mu__quant8 = TRUE;
{
for(int mu_j = 1; mu_j <= 2; mu_j++) {
bool mu__boolexpr9;
bool mu__boolexpr10;
  if (!((mu_Cache[mu_j].mu_State) != (mu_E))) mu__boolexpr10 = FALSE ;
  else {
  mu__boolexpr10 = ((mu_Chan2[mu_j].mu_Cmd) != (mu_GntE)) ; 
}
  if (!(mu__boolexpr10)) mu__boolexpr9 = FALSE ;
  else {
  mu__boolexpr9 = ((mu_Chan3[mu_j].mu_Cmd) != (mu_InvAck)) ; 
}
if ( !(mu__boolexpr9) )
  { mu__quant8 = FALSE; break; }
};
};
  mu__boolexpr6 = (mu__quant8) ; 
}
    return mu__boolexpr6;
  }

  void NextRule(unsigned & what_rule)
  {
    unsigned r = what_rule - 0;
    while (what_rule < 1 )
      {
	if ( ( TRUE  ) ) {
bool mu__boolexpr11;
bool mu__boolexpr12;
  if (!((mu_CurCmd) != (mu_Empty))) mu__boolexpr12 = FALSE ;
  else {
  mu__boolexpr12 = ((mu_ExGntd) == (mu_true)) ; 
}
  if (!(mu__boolexpr12)) mu__boolexpr11 = FALSE ;
  else {
bool mu__quant13; 
mu__quant13 = TRUE;
{
for(int mu_j = 1; mu_j <= 2; mu_j++) {
bool mu__boolexpr14;
bool mu__boolexpr15;
  if (!((mu_Cache[mu_j].mu_State) != (mu_E))) mu__boolexpr15 = FALSE ;
  else {
  mu__boolexpr15 = ((mu_Chan2[mu_j].mu_Cmd) != (mu_GntE)) ; 
}
  if (!(mu__boolexpr15)) mu__boolexpr14 = FALSE ;
  else {
  mu__boolexpr14 = ((mu_Chan3[mu_j].mu_Cmd) != (mu_InvAck)) ; 
}
if ( !(mu__boolexpr14) )
  { mu__quant13 = FALSE; break; }
};
};
  mu__boolexpr11 = (mu__quant13) ; 
}
	      if (mu__boolexpr11) {
		if ( ( TRUE  ) )
		  return;
		else
		  what_rule++;
	      }
	      else
		what_rule += 1;
	}
	else
	  what_rule += 1;
    r = what_rule - 0;
    }
  }

  void Code(unsigned r)
  {
mu_ExGntd = mu_false;
  };

};
/******************** RuleBase1 ********************/
class RuleBase1
{
public:
  int Priority()
  {
    return 0;
  }
  char * Name(unsigned r)
  {
    return tsprintf("ABS_RecvReqS");
  }
  bool Condition(unsigned r)
  {
    return (mu_CurCmd) == (mu_Empty);
  }

  void NextRule(unsigned & what_rule)
  {
    unsigned r = what_rule - 1;
    while (what_rule < 2 )
      {
	if ( ( TRUE  ) ) {
	      if ((mu_CurCmd) == (mu_Empty)) {
		if ( ( TRUE  ) )
		  return;
		else
		  what_rule++;
	      }
	      else
		what_rule += 1;
	}
	else
	  what_rule += 1;
    r = what_rule - 1;
    }
  }

  void Code(unsigned r)
  {
mu_CurCmd = mu_ReqS;
mu_CurPtr = mu_Other;
{
for(int mu_j = 1; mu_j <= 2; mu_j++) {
mu_InvSet[mu_j] = mu_ShrSet[mu_j];
};
};
  };

};
/******************** RuleBase2 ********************/
class RuleBase2
{
public:
  int Priority()
  {
    return 0;
  }
  char * Name(unsigned r)
  {
    return tsprintf("ABS_RecvReqE");
  }
  bool Condition(unsigned r)
  {
    return (mu_CurCmd) == (mu_Empty);
  }

  void NextRule(unsigned & what_rule)
  {
    unsigned r = what_rule - 2;
    while (what_rule < 3 )
      {
	if ( ( TRUE  ) ) {
	      if ((mu_CurCmd) == (mu_Empty)) {
		if ( ( TRUE  ) )
		  return;
		else
		  what_rule++;
	      }
	      else
		what_rule += 1;
	}
	else
	  what_rule += 1;
    r = what_rule - 2;
    }
  }

  void Code(unsigned r)
  {
mu_CurCmd = mu_ReqE;
mu_CurPtr = mu_Other;
{
for(int mu_j = 1; mu_j <= 2; mu_j++) {
mu_InvSet[mu_j] = mu_ShrSet[mu_j];
};
};
  };

};
/******************** RuleBase3 ********************/
class RuleBase3
{
public:
  int Priority()
  {
    return 0;
  }
  char * Name(unsigned r)
  {
    return tsprintf("ABS_SendGntS");
  }
  bool Condition(unsigned r)
  {
bool mu__boolexpr16;
bool mu__boolexpr17;
  if (!((mu_CurCmd) == (mu_ReqS))) mu__boolexpr17 = FALSE ;
  else {
  mu__boolexpr17 = ((mu_CurPtr) == (mu_Other)) ; 
}
  if (!(mu__boolexpr17)) mu__boolexpr16 = FALSE ;
  else {
  mu__boolexpr16 = ((mu_ExGntd) == (mu_false)) ; 
}
    return mu__boolexpr16;
  }

  void NextRule(unsigned & what_rule)
  {
    unsigned r = what_rule - 3;
    while (what_rule < 4 )
      {
	if ( ( TRUE  ) ) {
bool mu__boolexpr18;
bool mu__boolexpr19;
  if (!((mu_CurCmd) == (mu_ReqS))) mu__boolexpr19 = FALSE ;
  else {
  mu__boolexpr19 = ((mu_CurPtr) == (mu_Other)) ; 
}
  if (!(mu__boolexpr19)) mu__boolexpr18 = FALSE ;
  else {
  mu__boolexpr18 = ((mu_ExGntd) == (mu_false)) ; 
}
	      if (mu__boolexpr18) {
		if ( ( TRUE  ) )
		  return;
		else
		  what_rule++;
	      }
	      else
		what_rule += 1;
	}
	else
	  what_rule += 1;
    r = what_rule - 3;
    }
  }

  void Code(unsigned r)
  {
mu_CurCmd = mu_Empty;
  };

};
/******************** RuleBase4 ********************/
class RuleBase4
{
public:
  int Priority()
  {
    return 0;
  }
  char * Name(unsigned r)
  {
    return tsprintf("ABS_SendGntE");
  }
  bool Condition(unsigned r)
  {
bool mu__boolexpr20;
bool mu__boolexpr21;
bool mu__boolexpr22;
  if (!((mu_CurCmd) == (mu_ReqE))) mu__boolexpr22 = FALSE ;
  else {
  mu__boolexpr22 = ((mu_CurPtr) == (mu_Other)) ; 
}
  if (!(mu__boolexpr22)) mu__boolexpr21 = FALSE ;
  else {
  mu__boolexpr21 = ((mu_ExGntd) == (mu_false)) ; 
}
  if (!(mu__boolexpr21)) mu__boolexpr20 = FALSE ;
  else {
bool mu__quant23; 
mu__quant23 = TRUE;
{
for(int mu_j = 1; mu_j <= 2; mu_j++) {
if ( !((mu_ShrSet[mu_j]) == (mu_false)) )
  { mu__quant23 = FALSE; break; }
};
};
  mu__boolexpr20 = (mu__quant23) ; 
}
    return mu__boolexpr20;
  }

  void NextRule(unsigned & what_rule)
  {
    unsigned r = what_rule - 4;
    while (what_rule < 5 )
      {
	if ( ( TRUE  ) ) {
bool mu__boolexpr24;
bool mu__boolexpr25;
bool mu__boolexpr26;
  if (!((mu_CurCmd) == (mu_ReqE))) mu__boolexpr26 = FALSE ;
  else {
  mu__boolexpr26 = ((mu_CurPtr) == (mu_Other)) ; 
}
  if (!(mu__boolexpr26)) mu__boolexpr25 = FALSE ;
  else {
  mu__boolexpr25 = ((mu_ExGntd) == (mu_false)) ; 
}
  if (!(mu__boolexpr25)) mu__boolexpr24 = FALSE ;
  else {
bool mu__quant27; 
mu__quant27 = TRUE;
{
for(int mu_j = 1; mu_j <= 2; mu_j++) {
if ( !((mu_ShrSet[mu_j]) == (mu_false)) )
  { mu__quant27 = FALSE; break; }
};
};
  mu__boolexpr24 = (mu__quant27) ; 
}
	      if (mu__boolexpr24) {
		if ( ( TRUE  ) )
		  return;
		else
		  what_rule++;
	      }
	      else
		what_rule += 1;
	}
	else
	  what_rule += 1;
    r = what_rule - 4;
    }
  }

  void Code(unsigned r)
  {
mu_ExGntd = mu_true;
mu_CurCmd = mu_Empty;
mu_CurPtr.undefine();
  };

};
/******************** RuleBase5 ********************/
class RuleBase5
{
public:
  int Priority()
  {
    return 0;
  }
  char * Name(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    return tsprintf("SendReqS, i:%s", mu_i.Name());
  }
  bool Condition(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
bool mu__boolexpr28;
  if (!((mu_Chan1[mu_i].mu_Cmd) == (mu_Empty))) mu__boolexpr28 = FALSE ;
  else {
  mu__boolexpr28 = ((mu_Cache[mu_i].mu_State) == (mu_I)) ; 
}
    return mu__boolexpr28;
  }

  void NextRule(unsigned & what_rule)
  {
    unsigned r = what_rule - 5;
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    while (what_rule < 7 )
      {
	if ( ( TRUE  ) ) {
bool mu__boolexpr29;
  if (!((mu_Chan1[mu_i].mu_Cmd) == (mu_Empty))) mu__boolexpr29 = FALSE ;
  else {
  mu__boolexpr29 = ((mu_Cache[mu_i].mu_State) == (mu_I)) ; 
}
	      if (mu__boolexpr29) {
		if ( ( TRUE  ) )
		  return;
		else
		  what_rule++;
	      }
	      else
		what_rule += 1;
	}
	else
	  what_rule += 1;
    r = what_rule - 5;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    }
  }

  void Code(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
mu_Chan1[mu_i].mu_Cmd = mu_ReqS;
  };

};
/******************** RuleBase6 ********************/
class RuleBase6
{
public:
  int Priority()
  {
    return 0;
  }
  char * Name(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    return tsprintf("SendReqE, i:%s", mu_i.Name());
  }
  bool Condition(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
bool mu__boolexpr30;
  if (!((mu_Chan1[mu_i].mu_Cmd) == (mu_Empty))) mu__boolexpr30 = FALSE ;
  else {
bool mu__boolexpr31;
  if ((mu_Cache[mu_i].mu_State) == (mu_I)) mu__boolexpr31 = TRUE ;
  else {
  mu__boolexpr31 = ((mu_Cache[mu_i].mu_State) == (mu_S)) ; 
}
  mu__boolexpr30 = (mu__boolexpr31) ; 
}
    return mu__boolexpr30;
  }

  void NextRule(unsigned & what_rule)
  {
    unsigned r = what_rule - 7;
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    while (what_rule < 9 )
      {
	if ( ( TRUE  ) ) {
bool mu__boolexpr32;
  if (!((mu_Chan1[mu_i].mu_Cmd) == (mu_Empty))) mu__boolexpr32 = FALSE ;
  else {
bool mu__boolexpr33;
  if ((mu_Cache[mu_i].mu_State) == (mu_I)) mu__boolexpr33 = TRUE ;
  else {
  mu__boolexpr33 = ((mu_Cache[mu_i].mu_State) == (mu_S)) ; 
}
  mu__boolexpr32 = (mu__boolexpr33) ; 
}
	      if (mu__boolexpr32) {
		if ( ( TRUE  ) )
		  return;
		else
		  what_rule++;
	      }
	      else
		what_rule += 1;
	}
	else
	  what_rule += 1;
    r = what_rule - 7;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    }
  }

  void Code(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
mu_Chan1[mu_i].mu_Cmd = mu_ReqE;
  };

};
/******************** RuleBase7 ********************/
class RuleBase7
{
public:
  int Priority()
  {
    return 0;
  }
  char * Name(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    return tsprintf("RecvReqS, i:%s", mu_i.Name());
  }
  bool Condition(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
bool mu__boolexpr34;
  if (!((mu_CurCmd) == (mu_Empty))) mu__boolexpr34 = FALSE ;
  else {
  mu__boolexpr34 = ((mu_Chan1[mu_i].mu_Cmd) == (mu_ReqS)) ; 
}
    return mu__boolexpr34;
  }

  void NextRule(unsigned & what_rule)
  {
    unsigned r = what_rule - 9;
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    while (what_rule < 11 )
      {
	if ( ( TRUE  ) ) {
bool mu__boolexpr35;
  if (!((mu_CurCmd) == (mu_Empty))) mu__boolexpr35 = FALSE ;
  else {
  mu__boolexpr35 = ((mu_Chan1[mu_i].mu_Cmd) == (mu_ReqS)) ; 
}
	      if (mu__boolexpr35) {
		if ( ( TRUE  ) )
		  return;
		else
		  what_rule++;
	      }
	      else
		what_rule += 1;
	}
	else
	  what_rule += 1;
    r = what_rule - 9;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    }
  }

  void Code(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
mu_CurCmd = mu_ReqS;
mu_CurPtr = mu_i;
mu_Chan1[mu_i].mu_Cmd = mu_Empty;
{
for(int mu_j = 1; mu_j <= 2; mu_j++) {
mu_InvSet[mu_j] = mu_ShrSet[mu_j];
};
};
  };

};
/******************** RuleBase8 ********************/
class RuleBase8
{
public:
  int Priority()
  {
    return 0;
  }
  char * Name(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    return tsprintf("RecvReqE, i:%s", mu_i.Name());
  }
  bool Condition(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
bool mu__boolexpr36;
  if (!((mu_CurCmd) == (mu_Empty))) mu__boolexpr36 = FALSE ;
  else {
  mu__boolexpr36 = ((mu_Chan1[mu_i].mu_Cmd) == (mu_ReqE)) ; 
}
    return mu__boolexpr36;
  }

  void NextRule(unsigned & what_rule)
  {
    unsigned r = what_rule - 11;
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    while (what_rule < 13 )
      {
	if ( ( TRUE  ) ) {
bool mu__boolexpr37;
  if (!((mu_CurCmd) == (mu_Empty))) mu__boolexpr37 = FALSE ;
  else {
  mu__boolexpr37 = ((mu_Chan1[mu_i].mu_Cmd) == (mu_ReqE)) ; 
}
	      if (mu__boolexpr37) {
		if ( ( TRUE  ) )
		  return;
		else
		  what_rule++;
	      }
	      else
		what_rule += 1;
	}
	else
	  what_rule += 1;
    r = what_rule - 11;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    }
  }

  void Code(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
mu_CurCmd = mu_ReqE;
mu_CurPtr = mu_i;
mu_Chan1[mu_i].mu_Cmd = mu_Empty;
{
for(int mu_j = 1; mu_j <= 2; mu_j++) {
mu_InvSet[mu_j] = mu_ShrSet[mu_j];
};
};
  };

};
/******************** RuleBase9 ********************/
class RuleBase9
{
public:
  int Priority()
  {
    return 0;
  }
  char * Name(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    return tsprintf("SendInv, i:%s", mu_i.Name());
  }
  bool Condition(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
bool mu__boolexpr38;
bool mu__boolexpr39;
  if (!((mu_Chan2[mu_i].mu_Cmd) == (mu_Empty))) mu__boolexpr39 = FALSE ;
  else {
  mu__boolexpr39 = ((mu_InvSet[mu_i]) == (mu_true)) ; 
}
  if (!(mu__boolexpr39)) mu__boolexpr38 = FALSE ;
  else {
bool mu__boolexpr40;
  if ((mu_CurCmd) == (mu_ReqE)) mu__boolexpr40 = TRUE ;
  else {
bool mu__boolexpr41;
  if (!((mu_CurCmd) == (mu_ReqS))) mu__boolexpr41 = FALSE ;
  else {
  mu__boolexpr41 = ((mu_ExGntd) == (mu_true)) ; 
}
  mu__boolexpr40 = (mu__boolexpr41) ; 
}
  mu__boolexpr38 = (mu__boolexpr40) ; 
}
    return mu__boolexpr38;
  }

  void NextRule(unsigned & what_rule)
  {
    unsigned r = what_rule - 13;
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    while (what_rule < 15 )
      {
	if ( ( TRUE  ) ) {
bool mu__boolexpr42;
bool mu__boolexpr43;
  if (!((mu_Chan2[mu_i].mu_Cmd) == (mu_Empty))) mu__boolexpr43 = FALSE ;
  else {
  mu__boolexpr43 = ((mu_InvSet[mu_i]) == (mu_true)) ; 
}
  if (!(mu__boolexpr43)) mu__boolexpr42 = FALSE ;
  else {
bool mu__boolexpr44;
  if ((mu_CurCmd) == (mu_ReqE)) mu__boolexpr44 = TRUE ;
  else {
bool mu__boolexpr45;
  if (!((mu_CurCmd) == (mu_ReqS))) mu__boolexpr45 = FALSE ;
  else {
  mu__boolexpr45 = ((mu_ExGntd) == (mu_true)) ; 
}
  mu__boolexpr44 = (mu__boolexpr45) ; 
}
  mu__boolexpr42 = (mu__boolexpr44) ; 
}
	      if (mu__boolexpr42) {
		if ( ( TRUE  ) )
		  return;
		else
		  what_rule++;
	      }
	      else
		what_rule += 1;
	}
	else
	  what_rule += 1;
    r = what_rule - 13;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    }
  }

  void Code(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
mu_Chan2[mu_i].mu_Cmd = mu_Inv;
mu_InvSet[mu_i] = mu_false;
  };

};
/******************** RuleBase10 ********************/
class RuleBase10
{
public:
  int Priority()
  {
    return 0;
  }
  char * Name(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    return tsprintf("SendInvAck, i:%s", mu_i.Name());
  }
  bool Condition(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
bool mu__boolexpr46;
  if (!((mu_Chan2[mu_i].mu_Cmd) == (mu_Inv))) mu__boolexpr46 = FALSE ;
  else {
  mu__boolexpr46 = ((mu_Chan3[mu_i].mu_Cmd) == (mu_Empty)) ; 
}
    return mu__boolexpr46;
  }

  void NextRule(unsigned & what_rule)
  {
    unsigned r = what_rule - 15;
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    while (what_rule < 17 )
      {
	if ( ( TRUE  ) ) {
bool mu__boolexpr47;
  if (!((mu_Chan2[mu_i].mu_Cmd) == (mu_Inv))) mu__boolexpr47 = FALSE ;
  else {
  mu__boolexpr47 = ((mu_Chan3[mu_i].mu_Cmd) == (mu_Empty)) ; 
}
	      if (mu__boolexpr47) {
		if ( ( TRUE  ) )
		  return;
		else
		  what_rule++;
	      }
	      else
		what_rule += 1;
	}
	else
	  what_rule += 1;
    r = what_rule - 15;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    }
  }

  void Code(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
mu_Chan2[mu_i].mu_Cmd = mu_Empty;
mu_Chan3[mu_i].mu_Cmd = mu_InvAck;
mu_Cache[mu_i].mu_State = mu_I;
  };

};
/******************** RuleBase11 ********************/
class RuleBase11
{
public:
  int Priority()
  {
    return 0;
  }
  char * Name(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    return tsprintf("RecvInvAck2, i:%s", mu_i.Name());
  }
  bool Condition(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
bool mu__boolexpr48;
bool mu__boolexpr49;
  if (!((mu_Chan3[mu_i].mu_Cmd) == (mu_InvAck))) mu__boolexpr49 = FALSE ;
  else {
  mu__boolexpr49 = ((mu_CurCmd) != (mu_Empty)) ; 
}
  if (!(mu__boolexpr49)) mu__boolexpr48 = FALSE ;
  else {
  mu__boolexpr48 = ((mu_ExGntd) == (mu_false)) ; 
}
    return mu__boolexpr48;
  }

  void NextRule(unsigned & what_rule)
  {
    unsigned r = what_rule - 17;
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    while (what_rule < 19 )
      {
	if ( ( TRUE  ) ) {
bool mu__boolexpr50;
bool mu__boolexpr51;
  if (!((mu_Chan3[mu_i].mu_Cmd) == (mu_InvAck))) mu__boolexpr51 = FALSE ;
  else {
  mu__boolexpr51 = ((mu_CurCmd) != (mu_Empty)) ; 
}
  if (!(mu__boolexpr51)) mu__boolexpr50 = FALSE ;
  else {
  mu__boolexpr50 = ((mu_ExGntd) == (mu_false)) ; 
}
	      if (mu__boolexpr50) {
		if ( ( TRUE  ) )
		  return;
		else
		  what_rule++;
	      }
	      else
		what_rule += 1;
	}
	else
	  what_rule += 1;
    r = what_rule - 17;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    }
  }

  void Code(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
mu_Chan3[mu_i].mu_Cmd = mu_Empty;
mu_ShrSet[mu_i] = mu_false;
  };

};
/******************** RuleBase12 ********************/
class RuleBase12
{
public:
  int Priority()
  {
    return 0;
  }
  char * Name(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    return tsprintf("RecvInvAck1, i:%s", mu_i.Name());
  }
  bool Condition(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
bool mu__boolexpr52;
bool mu__boolexpr53;
  if (!((mu_Chan3[mu_i].mu_Cmd) == (mu_InvAck))) mu__boolexpr53 = FALSE ;
  else {
  mu__boolexpr53 = ((mu_CurCmd) != (mu_Empty)) ; 
}
  if (!(mu__boolexpr53)) mu__boolexpr52 = FALSE ;
  else {
  mu__boolexpr52 = ((mu_ExGntd) == (mu_true)) ; 
}
    return mu__boolexpr52;
  }

  void NextRule(unsigned & what_rule)
  {
    unsigned r = what_rule - 19;
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    while (what_rule < 21 )
      {
	if ( ( TRUE  ) ) {
bool mu__boolexpr54;
bool mu__boolexpr55;
  if (!((mu_Chan3[mu_i].mu_Cmd) == (mu_InvAck))) mu__boolexpr55 = FALSE ;
  else {
  mu__boolexpr55 = ((mu_CurCmd) != (mu_Empty)) ; 
}
  if (!(mu__boolexpr55)) mu__boolexpr54 = FALSE ;
  else {
  mu__boolexpr54 = ((mu_ExGntd) == (mu_true)) ; 
}
	      if (mu__boolexpr54) {
		if ( ( TRUE  ) )
		  return;
		else
		  what_rule++;
	      }
	      else
		what_rule += 1;
	}
	else
	  what_rule += 1;
    r = what_rule - 19;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    }
  }

  void Code(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
mu_Chan3[mu_i].mu_Cmd = mu_Empty;
mu_ShrSet[mu_i] = mu_false;
mu_ExGntd = mu_false;
  };

};
/******************** RuleBase13 ********************/
class RuleBase13
{
public:
  int Priority()
  {
    return 0;
  }
  char * Name(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    return tsprintf("SendGntS, i:%s", mu_i.Name());
  }
  bool Condition(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
bool mu__boolexpr56;
bool mu__boolexpr57;
bool mu__boolexpr58;
  if (!((mu_CurCmd) == (mu_ReqS))) mu__boolexpr58 = FALSE ;
  else {
  mu__boolexpr58 = ((mu_CurPtr) == (mu_i)) ; 
}
  if (!(mu__boolexpr58)) mu__boolexpr57 = FALSE ;
  else {
  mu__boolexpr57 = ((mu_Chan2[mu_i].mu_Cmd) == (mu_Empty)) ; 
}
  if (!(mu__boolexpr57)) mu__boolexpr56 = FALSE ;
  else {
  mu__boolexpr56 = ((mu_ExGntd) == (mu_false)) ; 
}
    return mu__boolexpr56;
  }

  void NextRule(unsigned & what_rule)
  {
    unsigned r = what_rule - 21;
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    while (what_rule < 23 )
      {
	if ( ( TRUE  ) ) {
bool mu__boolexpr59;
bool mu__boolexpr60;
bool mu__boolexpr61;
  if (!((mu_CurCmd) == (mu_ReqS))) mu__boolexpr61 = FALSE ;
  else {
  mu__boolexpr61 = ((mu_CurPtr) == (mu_i)) ; 
}
  if (!(mu__boolexpr61)) mu__boolexpr60 = FALSE ;
  else {
  mu__boolexpr60 = ((mu_Chan2[mu_i].mu_Cmd) == (mu_Empty)) ; 
}
  if (!(mu__boolexpr60)) mu__boolexpr59 = FALSE ;
  else {
  mu__boolexpr59 = ((mu_ExGntd) == (mu_false)) ; 
}
	      if (mu__boolexpr59) {
		if ( ( TRUE  ) )
		  return;
		else
		  what_rule++;
	      }
	      else
		what_rule += 1;
	}
	else
	  what_rule += 1;
    r = what_rule - 21;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    }
  }

  void Code(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
mu_Chan2[mu_i].mu_Cmd = mu_GntS;
mu_ShrSet[mu_i] = mu_true;
mu_CurCmd = mu_Empty;
  };

};
/******************** RuleBase14 ********************/
class RuleBase14
{
public:
  int Priority()
  {
    return 0;
  }
  char * Name(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    return tsprintf("SendGntE, i:%s", mu_i.Name());
  }
  bool Condition(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
bool mu__boolexpr62;
bool mu__boolexpr63;
bool mu__boolexpr64;
bool mu__boolexpr65;
  if (!((mu_CurCmd) == (mu_ReqE))) mu__boolexpr65 = FALSE ;
  else {
  mu__boolexpr65 = ((mu_CurPtr) == (mu_i)) ; 
}
  if (!(mu__boolexpr65)) mu__boolexpr64 = FALSE ;
  else {
  mu__boolexpr64 = ((mu_Chan2[mu_i].mu_Cmd) == (mu_Empty)) ; 
}
  if (!(mu__boolexpr64)) mu__boolexpr63 = FALSE ;
  else {
  mu__boolexpr63 = ((mu_ExGntd) == (mu_false)) ; 
}
  if (!(mu__boolexpr63)) mu__boolexpr62 = FALSE ;
  else {
bool mu__quant66; 
mu__quant66 = TRUE;
{
for(int mu_j = 1; mu_j <= 2; mu_j++) {
if ( !((mu_ShrSet[mu_j]) == (mu_false)) )
  { mu__quant66 = FALSE; break; }
};
};
  mu__boolexpr62 = (mu__quant66) ; 
}
    return mu__boolexpr62;
  }

  void NextRule(unsigned & what_rule)
  {
    unsigned r = what_rule - 23;
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    while (what_rule < 25 )
      {
	if ( ( TRUE  ) ) {
bool mu__boolexpr67;
bool mu__boolexpr68;
bool mu__boolexpr69;
bool mu__boolexpr70;
  if (!((mu_CurCmd) == (mu_ReqE))) mu__boolexpr70 = FALSE ;
  else {
  mu__boolexpr70 = ((mu_CurPtr) == (mu_i)) ; 
}
  if (!(mu__boolexpr70)) mu__boolexpr69 = FALSE ;
  else {
  mu__boolexpr69 = ((mu_Chan2[mu_i].mu_Cmd) == (mu_Empty)) ; 
}
  if (!(mu__boolexpr69)) mu__boolexpr68 = FALSE ;
  else {
  mu__boolexpr68 = ((mu_ExGntd) == (mu_false)) ; 
}
  if (!(mu__boolexpr68)) mu__boolexpr67 = FALSE ;
  else {
bool mu__quant71; 
mu__quant71 = TRUE;
{
for(int mu_j = 1; mu_j <= 2; mu_j++) {
if ( !((mu_ShrSet[mu_j]) == (mu_false)) )
  { mu__quant71 = FALSE; break; }
};
};
  mu__boolexpr67 = (mu__quant71) ; 
}
	      if (mu__boolexpr67) {
		if ( ( TRUE  ) )
		  return;
		else
		  what_rule++;
	      }
	      else
		what_rule += 1;
	}
	else
	  what_rule += 1;
    r = what_rule - 23;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    }
  }

  void Code(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
mu_Chan2[mu_i].mu_Cmd = mu_GntE;
mu_ShrSet[mu_i] = mu_true;
mu_ExGntd = mu_true;
mu_CurCmd = mu_Empty;
mu_CurPtr.undefine();
  };

};
/******************** RuleBase15 ********************/
class RuleBase15
{
public:
  int Priority()
  {
    return 0;
  }
  char * Name(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    return tsprintf("RecvGntS, i:%s", mu_i.Name());
  }
  bool Condition(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    return (mu_Chan2[mu_i].mu_Cmd) == (mu_GntS);
  }

  void NextRule(unsigned & what_rule)
  {
    unsigned r = what_rule - 25;
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    while (what_rule < 27 )
      {
	if ( ( TRUE  ) ) {
	      if ((mu_Chan2[mu_i].mu_Cmd) == (mu_GntS)) {
		if ( ( TRUE  ) )
		  return;
		else
		  what_rule++;
	      }
	      else
		what_rule += 1;
	}
	else
	  what_rule += 1;
    r = what_rule - 25;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    }
  }

  void Code(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
mu_Cache[mu_i].mu_State = mu_S;
mu_Chan2[mu_i].mu_Cmd = mu_Empty;
  };

};
/******************** RuleBase16 ********************/
class RuleBase16
{
public:
  int Priority()
  {
    return 0;
  }
  char * Name(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    return tsprintf("RecvGntE, i:%s", mu_i.Name());
  }
  bool Condition(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    return (mu_Chan2[mu_i].mu_Cmd) == (mu_GntE);
  }

  void NextRule(unsigned & what_rule)
  {
    unsigned r = what_rule - 27;
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    while (what_rule < 29 )
      {
	if ( ( TRUE  ) ) {
	      if ((mu_Chan2[mu_i].mu_Cmd) == (mu_GntE)) {
		if ( ( TRUE  ) )
		  return;
		else
		  what_rule++;
	      }
	      else
		what_rule += 1;
	}
	else
	  what_rule += 1;
    r = what_rule - 27;
    mu_i.value((r % 2) + 1);
    r = r / 2;
    }
  }

  void Code(unsigned r)
  {
    static mu_1_NODE mu_i;
    mu_i.value((r % 2) + 1);
    r = r / 2;
mu_Cache[mu_i].mu_State = mu_E;
mu_Chan2[mu_i].mu_Cmd = mu_Empty;
  };

};
class NextStateGenerator
{
  RuleBase0 R0;
  RuleBase1 R1;
  RuleBase2 R2;
  RuleBase3 R3;
  RuleBase4 R4;
  RuleBase5 R5;
  RuleBase6 R6;
  RuleBase7 R7;
  RuleBase8 R8;
  RuleBase9 R9;
  RuleBase10 R10;
  RuleBase11 R11;
  RuleBase12 R12;
  RuleBase13 R13;
  RuleBase14 R14;
  RuleBase15 R15;
  RuleBase16 R16;
public:
void SetNextEnabledRule(unsigned & what_rule)
{
  category = CONDITION;
  if (what_rule<1)
    { R0.NextRule(what_rule);
      if (what_rule<1) return; }
  if (what_rule>=1 && what_rule<2)
    { R1.NextRule(what_rule);
      if (what_rule<2) return; }
  if (what_rule>=2 && what_rule<3)
    { R2.NextRule(what_rule);
      if (what_rule<3) return; }
  if (what_rule>=3 && what_rule<4)
    { R3.NextRule(what_rule);
      if (what_rule<4) return; }
  if (what_rule>=4 && what_rule<5)
    { R4.NextRule(what_rule);
      if (what_rule<5) return; }
  if (what_rule>=5 && what_rule<7)
    { R5.NextRule(what_rule);
      if (what_rule<7) return; }
  if (what_rule>=7 && what_rule<9)
    { R6.NextRule(what_rule);
      if (what_rule<9) return; }
  if (what_rule>=9 && what_rule<11)
    { R7.NextRule(what_rule);
      if (what_rule<11) return; }
  if (what_rule>=11 && what_rule<13)
    { R8.NextRule(what_rule);
      if (what_rule<13) return; }
  if (what_rule>=13 && what_rule<15)
    { R9.NextRule(what_rule);
      if (what_rule<15) return; }
  if (what_rule>=15 && what_rule<17)
    { R10.NextRule(what_rule);
      if (what_rule<17) return; }
  if (what_rule>=17 && what_rule<19)
    { R11.NextRule(what_rule);
      if (what_rule<19) return; }
  if (what_rule>=19 && what_rule<21)
    { R12.NextRule(what_rule);
      if (what_rule<21) return; }
  if (what_rule>=21 && what_rule<23)
    { R13.NextRule(what_rule);
      if (what_rule<23) return; }
  if (what_rule>=23 && what_rule<25)
    { R14.NextRule(what_rule);
      if (what_rule<25) return; }
  if (what_rule>=25 && what_rule<27)
    { R15.NextRule(what_rule);
      if (what_rule<27) return; }
  if (what_rule>=27 && what_rule<29)
    { R16.NextRule(what_rule);
      if (what_rule<29) return; }
}
bool Condition(unsigned r)
{
  category = CONDITION;
  if (r<=0) return R0.Condition(r-0);
  if (r>=1 && r<=1) return R1.Condition(r-1);
  if (r>=2 && r<=2) return R2.Condition(r-2);
  if (r>=3 && r<=3) return R3.Condition(r-3);
  if (r>=4 && r<=4) return R4.Condition(r-4);
  if (r>=5 && r<=6) return R5.Condition(r-5);
  if (r>=7 && r<=8) return R6.Condition(r-7);
  if (r>=9 && r<=10) return R7.Condition(r-9);
  if (r>=11 && r<=12) return R8.Condition(r-11);
  if (r>=13 && r<=14) return R9.Condition(r-13);
  if (r>=15 && r<=16) return R10.Condition(r-15);
  if (r>=17 && r<=18) return R11.Condition(r-17);
  if (r>=19 && r<=20) return R12.Condition(r-19);
  if (r>=21 && r<=22) return R13.Condition(r-21);
  if (r>=23 && r<=24) return R14.Condition(r-23);
  if (r>=25 && r<=26) return R15.Condition(r-25);
  if (r>=27 && r<=28) return R16.Condition(r-27);
Error.Notrace("Internal: NextStateGenerator -- checking condition for nonexisting rule.");
return 0;}
void Code(unsigned r)
{
  if (r<=0) { R0.Code(r-0); return; } 
  if (r>=1 && r<=1) { R1.Code(r-1); return; } 
  if (r>=2 && r<=2) { R2.Code(r-2); return; } 
  if (r>=3 && r<=3) { R3.Code(r-3); return; } 
  if (r>=4 && r<=4) { R4.Code(r-4); return; } 
  if (r>=5 && r<=6) { R5.Code(r-5); return; } 
  if (r>=7 && r<=8) { R6.Code(r-7); return; } 
  if (r>=9 && r<=10) { R7.Code(r-9); return; } 
  if (r>=11 && r<=12) { R8.Code(r-11); return; } 
  if (r>=13 && r<=14) { R9.Code(r-13); return; } 
  if (r>=15 && r<=16) { R10.Code(r-15); return; } 
  if (r>=17 && r<=18) { R11.Code(r-17); return; } 
  if (r>=19 && r<=20) { R12.Code(r-19); return; } 
  if (r>=21 && r<=22) { R13.Code(r-21); return; } 
  if (r>=23 && r<=24) { R14.Code(r-23); return; } 
  if (r>=25 && r<=26) { R15.Code(r-25); return; } 
  if (r>=27 && r<=28) { R16.Code(r-27); return; } 
}
int Priority(unsigned short r)
{
  if (r<=0) { return R0.Priority(); } 
  if (r>=1 && r<=1) { return R1.Priority(); } 
  if (r>=2 && r<=2) { return R2.Priority(); } 
  if (r>=3 && r<=3) { return R3.Priority(); } 
  if (r>=4 && r<=4) { return R4.Priority(); } 
  if (r>=5 && r<=6) { return R5.Priority(); } 
  if (r>=7 && r<=8) { return R6.Priority(); } 
  if (r>=9 && r<=10) { return R7.Priority(); } 
  if (r>=11 && r<=12) { return R8.Priority(); } 
  if (r>=13 && r<=14) { return R9.Priority(); } 
  if (r>=15 && r<=16) { return R10.Priority(); } 
  if (r>=17 && r<=18) { return R11.Priority(); } 
  if (r>=19 && r<=20) { return R12.Priority(); } 
  if (r>=21 && r<=22) { return R13.Priority(); } 
  if (r>=23 && r<=24) { return R14.Priority(); } 
  if (r>=25 && r<=26) { return R15.Priority(); } 
  if (r>=27 && r<=28) { return R16.Priority(); } 
return 0;}
char * Name(unsigned r)
{
  if (r<=0) return R0.Name(r-0);
  if (r>=1 && r<=1) return R1.Name(r-1);
  if (r>=2 && r<=2) return R2.Name(r-2);
  if (r>=3 && r<=3) return R3.Name(r-3);
  if (r>=4 && r<=4) return R4.Name(r-4);
  if (r>=5 && r<=6) return R5.Name(r-5);
  if (r>=7 && r<=8) return R6.Name(r-7);
  if (r>=9 && r<=10) return R7.Name(r-9);
  if (r>=11 && r<=12) return R8.Name(r-11);
  if (r>=13 && r<=14) return R9.Name(r-13);
  if (r>=15 && r<=16) return R10.Name(r-15);
  if (r>=17 && r<=18) return R11.Name(r-17);
  if (r>=19 && r<=20) return R12.Name(r-19);
  if (r>=21 && r<=22) return R13.Name(r-21);
  if (r>=23 && r<=24) return R14.Name(r-23);
  if (r>=25 && r<=26) return R15.Name(r-25);
  if (r>=27 && r<=28) return R16.Name(r-27);
  return NULL;
}
};
const unsigned numrules = 29;

/********************
  parameter
 ********************/
#define RULES_IN_WORLD 29


/********************
  Startstate records
 ********************/
/******************** StartStateBase0 ********************/
class StartStateBase0
{
public:
  char * Name(unsigned short r)
  {
    return tsprintf("Init");
  }
  void Code(unsigned short r)
  {
{
for(int mu_i = 1; mu_i <= 2; mu_i++) {
mu_Chan1[mu_i].mu_Cmd = mu_Empty;
mu_Chan2[mu_i].mu_Cmd = mu_Empty;
mu_Chan3[mu_i].mu_Cmd = mu_Empty;
mu_Cache[mu_i].mu_State = mu_I;
mu_InvSet[mu_i] = mu_false;
mu_ShrSet[mu_i] = mu_false;
};
};
mu_ExGntd = mu_false;
mu_CurCmd = mu_Empty;
mu_CurPtr.undefine();
  };

};
class StartStateGenerator
{
  StartStateBase0 S0;
public:
void Code(unsigned short r)
{
  if (r<=0) { S0.Code(r-0); return; }
}
char * Name(unsigned short r)
{
  if (r<=0) return S0.Name(r-0);
  return NULL;
}
};
const rulerec startstates[] = {
{ NULL, NULL, NULL, FALSE},
};
unsigned short StartStateManager::numstartstates = 1;

/********************
  Invariant records
 ********************/
int mu__invariant_72() // Invariant "Lemma_1"
{
bool mu__quant73; 
mu__quant73 = TRUE;
{
for(int mu_p = 1; mu_p <= 2; mu_p++) {
bool mu__quant74; 
mu__quant74 = TRUE;
{
for(int mu_i = 1; mu_i <= 2; mu_i++) {
bool mu__boolexpr75;
bool mu__boolexpr76;
bool mu__boolexpr77;
  if (!((mu_Chan3[mu_i].mu_Cmd) == (mu_InvAck))) mu__boolexpr77 = FALSE ;
  else {
  mu__boolexpr77 = ((mu_CurCmd) != (mu_Empty)) ; 
}
  if (!(mu__boolexpr77)) mu__boolexpr76 = FALSE ;
  else {
  mu__boolexpr76 = ((mu_ExGntd) == (mu_true)) ; 
}
  if (!(mu__boolexpr76)) mu__boolexpr75 = TRUE ;
  else {
bool mu__quant78; 
mu__quant78 = TRUE;
{
for(int mu_j = 1; mu_j <= 2; mu_j++) {
bool mu__boolexpr79;
  if (!((mu_j) != (mu_i))) mu__boolexpr79 = TRUE ;
  else {
bool mu__boolexpr80;
bool mu__boolexpr81;
  if (!((mu_Cache[mu_j].mu_State) != (mu_E))) mu__boolexpr81 = FALSE ;
  else {
  mu__boolexpr81 = ((mu_Chan2[mu_j].mu_Cmd) != (mu_GntE)) ; 
}
  if (!(mu__boolexpr81)) mu__boolexpr80 = FALSE ;
  else {
  mu__boolexpr80 = ((mu_Chan3[mu_j].mu_Cmd) != (mu_InvAck)) ; 
}
  mu__boolexpr79 = (mu__boolexpr80) ; 
}
if ( !(mu__boolexpr79) )
  { mu__quant78 = FALSE; break; }
};
};
  mu__boolexpr75 = (mu__quant78) ; 
}
if ( !(mu__boolexpr75) )
  { mu__quant74 = FALSE; break; }
};
};
if ( !(mu__quant74) )
  { mu__quant73 = FALSE; break; }
};
};
return mu__quant73;
};

bool mu__condition_82() // Condition for Rule "Lemma_1"
{
  return mu__invariant_72( );
}

/**** end rule declaration ****/

int mu__invariant_83() // Invariant "CntrlProp"
{
bool mu__quant84; 
mu__quant84 = TRUE;
{
for(int mu_i = 1; mu_i <= 2; mu_i++) {
bool mu__quant85; 
mu__quant85 = TRUE;
{
for(int mu_j = 1; mu_j <= 2; mu_j++) {
bool mu__boolexpr86;
  if (!((mu_i) != (mu_j))) mu__boolexpr86 = TRUE ;
  else {
bool mu__boolexpr87;
bool mu__boolexpr88;
  if (!((mu_Cache[mu_i].mu_State) == (mu_E))) mu__boolexpr88 = TRUE ;
  else {
  mu__boolexpr88 = ((mu_Cache[mu_j].mu_State) == (mu_I)) ; 
}
  if (!(mu__boolexpr88)) mu__boolexpr87 = FALSE ;
  else {
bool mu__boolexpr89;
  if (!((mu_Cache[mu_i].mu_State) == (mu_S))) mu__boolexpr89 = TRUE ;
  else {
bool mu__boolexpr90;
  if ((mu_Cache[mu_j].mu_State) == (mu_I)) mu__boolexpr90 = TRUE ;
  else {
  mu__boolexpr90 = ((mu_Cache[mu_j].mu_State) == (mu_S)) ; 
}
  mu__boolexpr89 = (mu__boolexpr90) ; 
}
  mu__boolexpr87 = (mu__boolexpr89) ; 
}
  mu__boolexpr86 = (mu__boolexpr87) ; 
}
if ( !(mu__boolexpr86) )
  { mu__quant85 = FALSE; break; }
};
};
if ( !(mu__quant85) )
  { mu__quant84 = FALSE; break; }
};
};
return mu__quant84;
};

bool mu__condition_91() // Condition for Rule "CntrlProp"
{
  return mu__invariant_83( );
}

/**** end rule declaration ****/

const rulerec invariants[] = {
{"CntrlProp", &mu__condition_91, NULL, },
{"Lemma_1", &mu__condition_82, NULL, },
};
const unsigned short numinvariants = 2;

/********************
  Normal/Canonicalization for scalarset
 ********************/
/*
CurCmd:NoScalarset
ExGntd:NoScalarset
CurPtr:ScalarsetVariable
ShrSet:ScalarsetArrayOfFree
InvSet:ScalarsetArrayOfFree
Chan3:ScalarsetArrayOfFree
Chan2:ScalarsetArrayOfFree
Chan1:ScalarsetArrayOfFree
Cache:ScalarsetArrayOfFree
*/

/********************
Code for symmetry
 ********************/

/********************
 Permutation Set Class
 ********************/
class PermSet
{
public:
  // book keeping
  enum PresentationType {Simple, Explicit};
  PresentationType Presentation;

  void ResetToSimple();
  void ResetToExplicit();
  void SimpleToExplicit();
  void SimpleToOne();
  bool NextPermutation();

  void Print_in_size()
  { int ret=0; for (int i=0; i<count; i++) if (in[i]) ret++; cout << "in_size:" << ret << "\n"; }


  /********************
   Simple and efficient representation
   ********************/
  int class_mu_1_NODE[2];
  int undefined_class_mu_1_NODE;// has the highest class number

  void Print_class_mu_1_NODE();
  bool OnlyOneRemain_mu_1_NODE;
  bool MTO_class_mu_1_NODE()
  {
    int i,j;
    if (OnlyOneRemain_mu_1_NODE)
      return FALSE;
    for (i=0; i<2; i++)
      for (j=0; j<2; j++)
        if (i!=j && class_mu_1_NODE[i]== class_mu_1_NODE[j])
	    return TRUE;
    OnlyOneRemain_mu_1_NODE = TRUE;
    return FALSE;
  }
  bool AlreadyOnlyOneRemain;
  bool MoreThanOneRemain();


  /********************
   Explicit representation
  ********************/
  unsigned long size;
  unsigned long count;
  // in will be of product of factorial sizes for fast canonicalize
  // in will be of size 1 for reduced local memory canonicalize
  bool * in;

  // auxiliary for explicit representation

  // in/perm/revperm will be of factorial size for fast canonicalize
  // they will be of size 1 for reduced local memory canonicalize
  // second range will be size of the scalarset
  int * in_mu_1_NODE;
  typedef int arr_mu_1_NODE[2];
  arr_mu_1_NODE * perm_mu_1_NODE;
  arr_mu_1_NODE * revperm_mu_1_NODE;

  int size_mu_1_NODE[2];
  bool reversed_sorted_mu_1_NODE(int start, int end);
  void reverse_reversed_mu_1_NODE(int start, int end);

  // procedure for explicit representation
  bool ok0(mu_1_NODE* perm, int size, mu_1_NODE k);
  void GenPerm0(mu_1_NODE* perm, int size, unsigned long& index);

  // General procedure
  PermSet();
  bool In(int i) const { return in[i]; };
  void Add(int i) { for (int j=0; j<i; j++) in[j] = FALSE;};
  void Remove(int i) { in[i] = FALSE; };
};
void PermSet::Print_class_mu_1_NODE()
{
  cout << "class_mu_1_NODE:\t";
  for (int i=0; i<2; i++)
    cout << class_mu_1_NODE[i];
  cout << " " << undefined_class_mu_1_NODE << "\n";
}
bool PermSet::MoreThanOneRemain()
{
  int i,j;
  if (AlreadyOnlyOneRemain)
    return FALSE;
  else {
    for (i=0; i<2; i++)
      for (j=0; j<2; j++)
        if (i!=j && class_mu_1_NODE[i]== class_mu_1_NODE[j])
	    return TRUE;
  }
  AlreadyOnlyOneRemain = TRUE;
  return FALSE;
}
PermSet::PermSet()
: Presentation(Simple)
{
  int i,j,k;
  if (  args->sym_alg.mode == argsym_alg::Exhaustive_Fast_Canonicalize) {
    mu_1_NODE Perm0[2];

  /********************
   declaration of class variables
  ********************/
  in = new bool[2];
 in_mu_1_NODE = new int[2];
 perm_mu_1_NODE = new arr_mu_1_NODE[2];
 revperm_mu_1_NODE = new arr_mu_1_NODE[2];

    // Set perm and revperm
    count = 0;
    for (i=1; i<=2; i++)
      {
        Perm0[0].value(i);
        GenPerm0(Perm0, 1, count);
      }
    if (count!=2)
      Error.Error( "unable to initialize PermSet");
    for (i=0; i<2; i++)
      for (j=1; j<=2; j++)
        for (k=1; k<=2; k++)
          if (revperm_mu_1_NODE[i][k-1]==j)   // k - base 
            perm_mu_1_NODE[i][j-1]=k; // j - base 

    // setting up combination of permutations
    // for different scalarset
    int carry;
    int i_mu_1_NODE = 0;
    size = 2;
    count = 2;
    for (i=0; i<2; i++)
      {
        carry = 1;
        in[i]= TRUE;
      in_mu_1_NODE[i] = i_mu_1_NODE;
      i_mu_1_NODE += carry;
      if (i_mu_1_NODE >= 2) { i_mu_1_NODE = 0; carry = 1; } 
      else { carry = 0; } 
    }
  }
  else
  {

  /********************
   declaration of class variables
  ********************/
  in = new bool[1];
 in_mu_1_NODE = new int[1];
 perm_mu_1_NODE = new arr_mu_1_NODE[1];
 revperm_mu_1_NODE = new arr_mu_1_NODE[1];
  in[0] = TRUE;
    in_mu_1_NODE[0] = 0;
  }
}
void PermSet::ResetToSimple()
{
  int i;
  for (i=0; i<2; i++)
    class_mu_1_NODE[i]=0;
  undefined_class_mu_1_NODE=0;
  OnlyOneRemain_mu_1_NODE = FALSE;

  AlreadyOnlyOneRemain = FALSE;
  Presentation = Simple;
}
void PermSet::ResetToExplicit()
{
  for (int i=0; i<2; i++) in[i] = TRUE;
  Presentation = Explicit;
}
void PermSet::SimpleToExplicit()
{
  int i,j,k;
  int start, class_size;
  int start_mu_1_NODE[2];
  int size_mu_1_NODE[2];
  bool should_be_in_mu_1_NODE[2];

  // Setup range for mapping
  start = 0;
  for (j=0; j<=undefined_class_mu_1_NODE; j++) // class number
    {
      class_size = 0;
      for (k=0; k<2; k++) // step through class_mu_1_pid[k]
	if (class_mu_1_NODE[k]==j)
	  class_size++;
      for (k=0; k<2; k++) // step through class_mu_1_pid[k]
	if (class_mu_1_NODE[k]==j)
	  {
	    size_mu_1_NODE[k] = class_size;
	    start_mu_1_NODE[k] = start;
	  }
      start+=class_size;
    }

  // To be In or not to be
  for (i=0; i<2; i++) // set up
    should_be_in_mu_1_NODE[i] = TRUE;
  for (i=0; i<2; i++) // to be in or not to be
    for (k=0; k<2; k++) // step through class_mu_1_pid[k]
      if (! (perm_mu_1_NODE[i][k]-1 >=start_mu_1_NODE[k] 
	     && perm_mu_1_NODE[i][k]-1 < start_mu_1_NODE[k] + size_mu_1_NODE[k]) )
  	    {
	      should_be_in_mu_1_NODE[i] = FALSE;
	      break;
	    }

  // setup explicit representation 
  // Set perm and revperm
  for (i=0; i<2; i++)
    {
      in[i] = TRUE;
      if (in[i] && !should_be_in_mu_1_NODE[in_mu_1_NODE[i]]) in[i] = FALSE;
    }
  Presentation = Explicit;
  if (args->test_parameter1.value==0) Print_in_size();
}
void PermSet::SimpleToOne()
{
  int i,j,k;
  int class_size;
  int start;


  // Setup range for mapping
  start = 0;
  for (j=0; j<=undefined_class_mu_1_NODE; j++) // class number
    {
      class_size = 0;
      for (k=0; k<2; k++) // step through class_mu_1_pid[k]
	if (class_mu_1_NODE[k]==j)
	  class_size++;
      for (k=0; k<2; k++) // step through class_mu_1_pid[k]
	if (class_mu_1_NODE[k]==j)
	  {
	    size_mu_1_NODE[k] = class_size;
	  }
      start+=class_size;
    }
  start = 0;
  for (j=0; j<=undefined_class_mu_1_NODE; j++) // class number
    {
      for (k=0; k<2; k++) // step through class_mu_1_pid[k]
	    if (class_mu_1_NODE[k]==j)
	      revperm_mu_1_NODE[0][start++] = k+1;
    }
  for (j=0; j<2; j++)
    for (k=0; k<2; k++)
      if (revperm_mu_1_NODE[0][k]==j+1)
        perm_mu_1_NODE[0][j]=k+1;
  Presentation = Explicit;
}
bool PermSet::ok0(mu_1_NODE* Perm, int size, mu_1_NODE k)
{
  for (int i=0; i<size; i++)
    if(Perm[i].value()==k)
      return FALSE;
  return TRUE;
}
void PermSet::GenPerm0(mu_1_NODE* Perm,int size, unsigned long& count)
{
  int i;
  if (size!=2)
    {
      for (i=1; i<=2; i++)
        if(ok0(Perm,size,i))
          {
            Perm[size].value(i);
            GenPerm0(Perm, size+1, count);
          }
    }
  else
    {
      for (i=1; i<=2; i++)
        revperm_mu_1_NODE[count][i-1]=Perm[i-1].value();// i - base
      count++;
    }
}
bool PermSet::reversed_sorted_mu_1_NODE(int start, int end)
{
  int i,j;

  for (i=start; i<end; i++)
    if (revperm_mu_1_NODE[0][i]<revperm_mu_1_NODE[0][i+1])
      return FALSE;
  return TRUE;
}
void PermSet::reverse_reversed_mu_1_NODE(int start, int end)
{
  int i,j;
  int temp;

  for (i=start, j=end; i<j; i++,j--) 
    {
      temp = revperm_mu_1_NODE[0][j];
      revperm_mu_1_NODE[0][j] = revperm_mu_1_NODE[0][i];
      revperm_mu_1_NODE[0][i] = temp;
    }
}
bool PermSet::NextPermutation()
{
  bool nexted = FALSE;
  int start, end; 
  int class_size;
  int temp;
  int j,k;

  // algorithm
  // for each class
  //   if forall in the same class reverse_sorted, 
  //     { sort again; goto next class }
  //   else
  //     {
  //       nexted = TRUE;
  //       for (j from l to r)
  // 	       if (for all j+ are reversed sorted)
  // 	         {
  // 	           swap j, j+1
  // 	           sort all j+ again
  // 	           break;
  // 	         }
  //     }
  for (start = 0; start < 2; )
    {
      end = start-1+size_mu_1_NODE[revperm_mu_1_NODE[0][start]-1];
      if (reversed_sorted_mu_1_NODE(start,end))
	       {
	  reverse_reversed_mu_1_NODE(start,end);
	  start = end+1;
	}
      else
	{
	  nexted = TRUE;
	  for (j = start; j<end; j++)
	    {
	      if (reversed_sorted_mu_1_NODE(j+1,end))
		{
		  for (k = end; k>j; k--)
		    {
		      if (revperm_mu_1_NODE[0][j]<revperm_mu_1_NODE[0][k])
			{
			  // swap j, k
			  temp = revperm_mu_1_NODE[0][j];
			  revperm_mu_1_NODE[0][j] = revperm_mu_1_NODE[0][k];
			  revperm_mu_1_NODE[0][k] = temp;
			  break;
			}
		    }
		  reverse_reversed_mu_1_NODE(j+1,end);
		  break;
		}
	    }
	  break;
	}
    }
if (!nexted) return FALSE;
  for (j=0; j<2; j++)
    for (k=0; k<2; k++)
      if (revperm_mu_1_NODE[0][k]==j+1)   // k - base 
	perm_mu_1_NODE[0][j]=k+1; // j - base 
  return TRUE;
}

/********************
 Symmetry Class
 ********************/
class SymmetryClass
{
  PermSet Perm;
  bool BestInitialized;
  state BestPermutedState;

  // utilities
  void SetBestResult(int i, state* temp);
  void ResetBestResult() {BestInitialized = FALSE;};

public:
  // initializer
  SymmetryClass() : Perm(), BestInitialized(FALSE) {};
  ~SymmetryClass() {};

  void Normalize(state* s);

  void Exhaustive_Fast_Canonicalize(state *s);
  void Heuristic_Fast_Canonicalize(state *s);
  void Heuristic_Small_Mem_Canonicalize(state *s);
  void Heuristic_Fast_Normalize(state *s);

  void MultisetSort(state* s);
};


/********************
 Symmetry Class Members
 ********************/
void SymmetryClass::MultisetSort(state* s)
{
        mu_CurCmd.MultisetSort();
        mu_ExGntd.MultisetSort();
        mu_CurPtr.MultisetSort();
        mu_ShrSet.MultisetSort();
        mu_InvSet.MultisetSort();
        mu_Chan3.MultisetSort();
        mu_Chan2.MultisetSort();
        mu_Chan1.MultisetSort();
        mu_Cache.MultisetSort();
}
void SymmetryClass::Normalize(state* s)
{
  switch (args->sym_alg.mode) {
  case argsym_alg::Exhaustive_Fast_Canonicalize:
    Exhaustive_Fast_Canonicalize(s);
    break;
  case argsym_alg::Heuristic_Fast_Canonicalize:
    Heuristic_Fast_Canonicalize(s);
    break;
  case argsym_alg::Heuristic_Small_Mem_Canonicalize:
    Heuristic_Small_Mem_Canonicalize(s);
    break;
  case argsym_alg::Heuristic_Fast_Normalize:
    Heuristic_Fast_Normalize(s);
    break;
  default:
    Heuristic_Fast_Canonicalize(s);
  }
}

/********************
 Permute and Canonicalize function for different types
 ********************/
void mu_1_NODE::Permute(PermSet& Perm, int i)
{
  if (Perm.Presentation != PermSet::Explicit)
    Error.Error("Internal Error: Wrong Sequence of Normalization");
  if (defined())
    value(Perm.perm_mu_1_NODE[Perm.in_mu_1_NODE[i]][value()-1]); // value - base
};
void mu_1_NODE::SimpleCanonicalize(PermSet& Perm)
{
  int i, class_number;
  if (Perm.Presentation != PermSet::Simple)
    Error.Error("Internal Error: Wrong Sequence of Normalization");

  if (defined())
    if (Perm.class_mu_1_NODE[value()-1]==Perm.undefined_class_mu_1_NODE) // value - base
      {
        // it has not been mapped to any particular value
        for (i=0; i<2; i++)
          if (Perm.class_mu_1_NODE[i] == Perm.undefined_class_mu_1_NODE && i!=value()-1)
            Perm.class_mu_1_NODE[i]++;
        value(1 + Perm.undefined_class_mu_1_NODE++);
      }
    else 
      {
        value(Perm.class_mu_1_NODE[value()-1]+1);
      }
}
void mu_1_NODE::Canonicalize(PermSet& Perm)
{
  Error.Error("Calling canonicalize() for Scalarset.");
}
void mu_1_NODE::SimpleLimit(PermSet& Perm)
{
  int i, class_number;
  if (Perm.Presentation != PermSet::Simple)
    Error.Error("Internal Error: Wrong Sequence of Normalization");

  if (defined())
    if (Perm.class_mu_1_NODE[value()-1]==Perm.undefined_class_mu_1_NODE) // value - base
      {
        // it has not been mapped to any particular value
        for (i=0; i<2; i++)
          if (Perm.class_mu_1_NODE[i] == Perm.undefined_class_mu_1_NODE && i!=value()-1)
            Perm.class_mu_1_NODE[i]++;
        Perm.undefined_class_mu_1_NODE++;
      }
}
void mu_1_NODE::ArrayLimit(PermSet& Perm) {}
void mu_1_NODE::Limit(PermSet& Perm) {}
void mu_1_NODE::MultisetLimit(PermSet& Perm)
{ Error.Error("Internal: calling MultisetLimit for scalarset type.\n"); };
void mu_1_OTHER::Permute(PermSet& Perm, int i) {};
void mu_1_OTHER::SimpleCanonicalize(PermSet& Perm) {};
void mu_1_OTHER::Canonicalize(PermSet& Perm) {};
void mu_1_OTHER::SimpleLimit(PermSet& Perm) {};
void mu_1_OTHER::ArrayLimit(PermSet& Perm) {};
void mu_1_OTHER::Limit(PermSet& Perm) {};
void mu_1_OTHER::MultisetLimit(PermSet& Perm)
{ Error.Error("Internal: calling MultisetLimit for enum type.\n"); };
void mu_1_ABS_NODE::Permute(PermSet& Perm, int i)
{
  if (Perm.Presentation != PermSet::Explicit)
    Error.Error("Internal Error: Wrong Sequence of Normalization");
  if (defined()) {
    if ( ( value() >= 1 ) && ( value() <= 2 ) )
      value(Perm.perm_mu_1_NODE[Perm.in_mu_1_NODE[i]][value()-1]+(0)); // value - base
  }
}
void mu_1_ABS_NODE::SimpleCanonicalize(PermSet& Perm)
{
  int i, class_number;
  if (Perm.Presentation != PermSet::Simple)
    Error.Error("Internal Error: Wrong Sequence of Normalization");
  if (defined()) {
    if ( ( value() >= 1 ) && ( value() <= 2 ) )
      {
        if (Perm.class_mu_1_NODE[value()-1]==Perm.undefined_class_mu_1_NODE) // value - base
          {
            // it has not been mapped to any particular value
            for (i=0; i<2; i++)
              if (Perm.class_mu_1_NODE[i] == Perm.undefined_class_mu_1_NODE && i!=value()-1)
                Perm.class_mu_1_NODE[i]++;
            value(1 + Perm.undefined_class_mu_1_NODE++);
          }
        else 
          {
            value(Perm.class_mu_1_NODE[value()-1]+1);
          }
      }
  }
}
void mu_1_ABS_NODE::Canonicalize(PermSet& Perm)
{
  Error.Error("Calling canonicalize() for Scalarset.");
}
void mu_1_ABS_NODE::SimpleLimit(PermSet& Perm)
{
  int i, class_number;
  if (Perm.Presentation != PermSet::Simple)
    Error.Error("Internal Error: Wrong Sequence of Normalization");
  if (defined()) {
    if ( ( value() >= 1 ) && ( value() <= 2 ) )
      if (Perm.class_mu_1_NODE[value()-1]==Perm.undefined_class_mu_1_NODE) // value - base
        {
          // it has not been mapped to any particular value
          for (i=0; i<2; i++)
            if (Perm.class_mu_1_NODE[i] == Perm.undefined_class_mu_1_NODE && i!=value()-1)
              Perm.class_mu_1_NODE[i]++;
          Perm.undefined_class_mu_1_NODE++;
        }
  }
}
void mu_1_ABS_NODE::ArrayLimit(PermSet& Perm) {}
void mu_1_ABS_NODE::Limit(PermSet& Perm) {}
void mu_1_ABS_NODE::MultisetLimit(PermSet& Perm)
{ Error.Error("Internal: calling MultisetLimit for union type.\n"); };
void mu_1_CACHE_STATE::Permute(PermSet& Perm, int i) {};
void mu_1_CACHE_STATE::SimpleCanonicalize(PermSet& Perm) {};
void mu_1_CACHE_STATE::Canonicalize(PermSet& Perm) {};
void mu_1_CACHE_STATE::SimpleLimit(PermSet& Perm) {};
void mu_1_CACHE_STATE::ArrayLimit(PermSet& Perm) {};
void mu_1_CACHE_STATE::Limit(PermSet& Perm) {};
void mu_1_CACHE_STATE::MultisetLimit(PermSet& Perm)
{ Error.Error("Internal: calling MultisetLimit for enum type.\n"); };
void mu_1_CACHE::Permute(PermSet& Perm, int i)
{
};
void mu_1_CACHE::SimpleCanonicalize(PermSet& Perm)
{ Error.Error("Internal: Simple Canonicalization of Record with no scalarset variable\n"); };
void mu_1_CACHE::Canonicalize(PermSet& Perm)
{
};
void mu_1_CACHE::SimpleLimit(PermSet& Perm){}
void mu_1_CACHE::ArrayLimit(PermSet& Perm){}
void mu_1_CACHE::Limit(PermSet& Perm)
{
};
void mu_1_CACHE::MultisetLimit(PermSet& Perm)
{
};
void mu_1_MSG_CMD::Permute(PermSet& Perm, int i) {};
void mu_1_MSG_CMD::SimpleCanonicalize(PermSet& Perm) {};
void mu_1_MSG_CMD::Canonicalize(PermSet& Perm) {};
void mu_1_MSG_CMD::SimpleLimit(PermSet& Perm) {};
void mu_1_MSG_CMD::ArrayLimit(PermSet& Perm) {};
void mu_1_MSG_CMD::Limit(PermSet& Perm) {};
void mu_1_MSG_CMD::MultisetLimit(PermSet& Perm)
{ Error.Error("Internal: calling MultisetLimit for enum type.\n"); };
void mu_1_MSG::Permute(PermSet& Perm, int i)
{
};
void mu_1_MSG::SimpleCanonicalize(PermSet& Perm)
{ Error.Error("Internal: Simple Canonicalization of Record with no scalarset variable\n"); };
void mu_1_MSG::Canonicalize(PermSet& Perm)
{
};
void mu_1_MSG::SimpleLimit(PermSet& Perm){}
void mu_1_MSG::ArrayLimit(PermSet& Perm){}
void mu_1_MSG::Limit(PermSet& Perm)
{
};
void mu_1_MSG::MultisetLimit(PermSet& Perm)
{
};
void mu_1__type_0::Permute(PermSet& Perm, int i)
{
  static mu_1__type_0 temp("Permute_mu_1__type_0",-1);
  int j;
  for (j=0; j<2; j++)
    array[j].Permute(Perm, i);
  temp = *this;
  for (j=1; j<=2; j++)
    (*this)[j] = temp[Perm.revperm_mu_1_NODE[Perm.in_mu_1_NODE[i]][j-1]];};
void mu_1__type_0::SimpleCanonicalize(PermSet& Perm)
{ Error.Error("Internal: Simple Canonicalization of Scalarset Array\n"); };
void mu_1__type_0::Canonicalize(PermSet& Perm)
{
  // indexes
  int i,j,k,z;
  // sorting
  int count_mu_1_NODE;
  int compare;
  static mu_1_CACHE value[2];
  // limit
  bool exists;
  bool split;
  bool goodset_mu_1_NODE[2];
  bool pos_mu_1_NODE[2][2];
  // range mapping
  int start;
  int class_size;
  int size_mu_1_NODE[2];
  int start_mu_1_NODE[2];
  // canonicalization
  static mu_1__type_0 temp;
  // sorting mu_1_NODE
  // only if there is more than 1 permutation in class
  if (Perm.MTO_class_mu_1_NODE())
    {
      for (i=0; i<2; i++)
        for (j=0; j<2; j++)
          pos_mu_1_NODE[i][j]=FALSE;
      count_mu_1_NODE = 0;
      for (i=0; i<2; i++)
        {
          for (j=0; j<count_mu_1_NODE; j++)
            {
              compare = CompareWeight(value[j],(*this)[i+1]);
              if (compare==0)
                {
                  pos_mu_1_NODE[j][i]= TRUE;
                  break;
                }
              else if (compare>0)
                {
                  for (k=count_mu_1_NODE; k>j; k--)
                    {
                      value[k] = value[k-1];
                      for (z=0; z<2; z++)
                        pos_mu_1_NODE[k][z] = pos_mu_1_NODE[k-1][z];
                    }
                  value[j] = (*this)[i+1];
                  for (z=0; z<2; z++)
                    pos_mu_1_NODE[j][z] = FALSE;
                  pos_mu_1_NODE[j][i] = TRUE;
                  count_mu_1_NODE++;
                  break;
                }
            }
          if (j==count_mu_1_NODE)
            {
              value[j] = (*this)[i+1];
              for (z=0; z<2; z++)
                pos_mu_1_NODE[j][z] = FALSE;
              pos_mu_1_NODE[j][i] = TRUE;
              count_mu_1_NODE++;
            }
        }
    }
  // if there is more than 1 permutation in class
  if (Perm.MTO_class_mu_1_NODE() && count_mu_1_NODE>1)
    {
      // limit
      for (j=0; j<2; j++) // class priority
        {
          for (i=0; i<count_mu_1_NODE; i++) // for value priority
            {
              exists = FALSE;
              for (k=0; k<2; k++) // step through class
                goodset_mu_1_NODE[k] = FALSE;
              for (k=0; k<2; k++) // step through class
                if (pos_mu_1_NODE[i][k] && Perm.class_mu_1_NODE[k] == j)
                  {
                    exists = TRUE;
                    goodset_mu_1_NODE[k] = TRUE;
                    pos_mu_1_NODE[i][k] = FALSE;
                  }
              if (exists)
                {
                  split=FALSE;
                  for (k=0; k<2; k++)
                    if ( Perm.class_mu_1_NODE[k] == j && !goodset_mu_1_NODE[k] ) 
                      split= TRUE;
                  if (split)
                    {
                      for (k=0; k<2; k++)
                        if (Perm.class_mu_1_NODE[k]>j
                            || ( Perm.class_mu_1_NODE[k] == j && !goodset_mu_1_NODE[k] ) )
                          Perm.class_mu_1_NODE[k]++;
                      Perm.undefined_class_mu_1_NODE++;
                    }
                }
            }
        }
    }
  if (Perm.MTO_class_mu_1_NODE())
    {

      // setup range for maping
      start = 0;
      for (j=0; j<=Perm.undefined_class_mu_1_NODE; j++) // class number
        {
          class_size = 0;
          for (k=0; k<2; k++) // step through class[k]
            if (Perm.class_mu_1_NODE[k]==j)
              class_size++;
          for (k=0; k<2; k++) // step through class[k]
            if (Perm.class_mu_1_NODE[k]==j)
              {
                size_mu_1_NODE[k] = class_size;
                start_mu_1_NODE[k] = start;
              }
          start+=class_size;
        }

      // canonicalize
      temp = *this;
      for (i=0; i<2; i++)
        for (j=0; j<2; j++)
         if (i >=start_mu_1_NODE[j] 
             && i < start_mu_1_NODE[j] + size_mu_1_NODE[j])
           {
             array[i+0] = temp[j+1];
             break;
           }
    }
  else
    {

      // fast canonicalize
      temp = *this;
      for (j=0; j<2; j++)
        array[Perm.class_mu_1_NODE[j]+0] = temp[j+1];
    }
}
void mu_1__type_0::SimpleLimit(PermSet& Perm){}
void mu_1__type_0::ArrayLimit(PermSet& Perm)
{
  // indexes
  int i,j,k,z;
  // sorting
  int count_mu_1_NODE;
  int compare;
  static mu_1_CACHE value[2];
  // limit
  bool exists;
  bool split;
  bool goodset_mu_1_NODE[2];
  bool pos_mu_1_NODE[2][2];
  // sorting mu_1_NODE
  // only if there is more than 1 permutation in class
  if (Perm.MTO_class_mu_1_NODE())
    {
      for (i=0; i<2; i++)
        for (j=0; j<2; j++)
          pos_mu_1_NODE[i][j]=FALSE;
      count_mu_1_NODE = 0;
      for (i=0; i<2; i++)
        {
          for (j=0; j<count_mu_1_NODE; j++)
            {
              compare = CompareWeight(value[j],(*this)[i+1]);
              if (compare==0)
                {
                  pos_mu_1_NODE[j][i]= TRUE;
                  break;
                }
              else if (compare>0)
                {
                  for (k=count_mu_1_NODE; k>j; k--)
                    {
                      value[k] = value[k-1];
                      for (z=0; z<2; z++)
                        pos_mu_1_NODE[k][z] = pos_mu_1_NODE[k-1][z];
                    }
                  value[j] = (*this)[i+1];
                  for (z=0; z<2; z++)
                    pos_mu_1_NODE[j][z] = FALSE;
                  pos_mu_1_NODE[j][i] = TRUE;
                  count_mu_1_NODE++;
                  break;
                }
            }
          if (j==count_mu_1_NODE)
            {
              value[j] = (*this)[i+1];
              for (z=0; z<2; z++)
                pos_mu_1_NODE[j][z] = FALSE;
              pos_mu_1_NODE[j][i] = TRUE;
              count_mu_1_NODE++;
            }
        }
    }
  // if there is more than 1 permutation in class
  if (Perm.MTO_class_mu_1_NODE() && count_mu_1_NODE>1)
    {
      // limit
      for (j=0; j<2; j++) // class priority
        {
          for (i=0; i<count_mu_1_NODE; i++) // for value priority
            {
              exists = FALSE;
              for (k=0; k<2; k++) // step through class
                goodset_mu_1_NODE[k] = FALSE;
              for (k=0; k<2; k++) // step through class
                if (pos_mu_1_NODE[i][k] && Perm.class_mu_1_NODE[k] == j)
                  {
                    exists = TRUE;
                    goodset_mu_1_NODE[k] = TRUE;
                    pos_mu_1_NODE[i][k] = FALSE;
                  }
              if (exists)
                {
                  split=FALSE;
                  for (k=0; k<2; k++)
                    if ( Perm.class_mu_1_NODE[k] == j && !goodset_mu_1_NODE[k] ) 
                      split= TRUE;
                  if (split)
                    {
                      for (k=0; k<2; k++)
                        if (Perm.class_mu_1_NODE[k]>j
                            || ( Perm.class_mu_1_NODE[k] == j && !goodset_mu_1_NODE[k] ) )
                          Perm.class_mu_1_NODE[k]++;
                      Perm.undefined_class_mu_1_NODE++;
                    }
                }
            }
        }
    }
}
void mu_1__type_0::Limit(PermSet& Perm){}
void mu_1__type_0::MultisetLimit(PermSet& Perm)
{ Error.Error("Internal: calling MultisetLimit for scalarset array.\n"); };
void mu_1__type_1::Permute(PermSet& Perm, int i)
{
  static mu_1__type_1 temp("Permute_mu_1__type_1",-1);
  int j;
  for (j=0; j<2; j++)
    array[j].Permute(Perm, i);
  temp = *this;
  for (j=1; j<=2; j++)
    (*this)[j] = temp[Perm.revperm_mu_1_NODE[Perm.in_mu_1_NODE[i]][j-1]];};
void mu_1__type_1::SimpleCanonicalize(PermSet& Perm)
{ Error.Error("Internal: Simple Canonicalization of Scalarset Array\n"); };
void mu_1__type_1::Canonicalize(PermSet& Perm)
{
  // indexes
  int i,j,k,z;
  // sorting
  int count_mu_1_NODE;
  int compare;
  static mu_1_MSG value[2];
  // limit
  bool exists;
  bool split;
  bool goodset_mu_1_NODE[2];
  bool pos_mu_1_NODE[2][2];
  // range mapping
  int start;
  int class_size;
  int size_mu_1_NODE[2];
  int start_mu_1_NODE[2];
  // canonicalization
  static mu_1__type_1 temp;
  // sorting mu_1_NODE
  // only if there is more than 1 permutation in class
  if (Perm.MTO_class_mu_1_NODE())
    {
      for (i=0; i<2; i++)
        for (j=0; j<2; j++)
          pos_mu_1_NODE[i][j]=FALSE;
      count_mu_1_NODE = 0;
      for (i=0; i<2; i++)
        {
          for (j=0; j<count_mu_1_NODE; j++)
            {
              compare = CompareWeight(value[j],(*this)[i+1]);
              if (compare==0)
                {
                  pos_mu_1_NODE[j][i]= TRUE;
                  break;
                }
              else if (compare>0)
                {
                  for (k=count_mu_1_NODE; k>j; k--)
                    {
                      value[k] = value[k-1];
                      for (z=0; z<2; z++)
                        pos_mu_1_NODE[k][z] = pos_mu_1_NODE[k-1][z];
                    }
                  value[j] = (*this)[i+1];
                  for (z=0; z<2; z++)
                    pos_mu_1_NODE[j][z] = FALSE;
                  pos_mu_1_NODE[j][i] = TRUE;
                  count_mu_1_NODE++;
                  break;
                }
            }
          if (j==count_mu_1_NODE)
            {
              value[j] = (*this)[i+1];
              for (z=0; z<2; z++)
                pos_mu_1_NODE[j][z] = FALSE;
              pos_mu_1_NODE[j][i] = TRUE;
              count_mu_1_NODE++;
            }
        }
    }
  // if there is more than 1 permutation in class
  if (Perm.MTO_class_mu_1_NODE() && count_mu_1_NODE>1)
    {
      // limit
      for (j=0; j<2; j++) // class priority
        {
          for (i=0; i<count_mu_1_NODE; i++) // for value priority
            {
              exists = FALSE;
              for (k=0; k<2; k++) // step through class
                goodset_mu_1_NODE[k] = FALSE;
              for (k=0; k<2; k++) // step through class
                if (pos_mu_1_NODE[i][k] && Perm.class_mu_1_NODE[k] == j)
                  {
                    exists = TRUE;
                    goodset_mu_1_NODE[k] = TRUE;
                    pos_mu_1_NODE[i][k] = FALSE;
                  }
              if (exists)
                {
                  split=FALSE;
                  for (k=0; k<2; k++)
                    if ( Perm.class_mu_1_NODE[k] == j && !goodset_mu_1_NODE[k] ) 
                      split= TRUE;
                  if (split)
                    {
                      for (k=0; k<2; k++)
                        if (Perm.class_mu_1_NODE[k]>j
                            || ( Perm.class_mu_1_NODE[k] == j && !goodset_mu_1_NODE[k] ) )
                          Perm.class_mu_1_NODE[k]++;
                      Perm.undefined_class_mu_1_NODE++;
                    }
                }
            }
        }
    }
  if (Perm.MTO_class_mu_1_NODE())
    {

      // setup range for maping
      start = 0;
      for (j=0; j<=Perm.undefined_class_mu_1_NODE; j++) // class number
        {
          class_size = 0;
          for (k=0; k<2; k++) // step through class[k]
            if (Perm.class_mu_1_NODE[k]==j)
              class_size++;
          for (k=0; k<2; k++) // step through class[k]
            if (Perm.class_mu_1_NODE[k]==j)
              {
                size_mu_1_NODE[k] = class_size;
                start_mu_1_NODE[k] = start;
              }
          start+=class_size;
        }

      // canonicalize
      temp = *this;
      for (i=0; i<2; i++)
        for (j=0; j<2; j++)
         if (i >=start_mu_1_NODE[j] 
             && i < start_mu_1_NODE[j] + size_mu_1_NODE[j])
           {
             array[i+0] = temp[j+1];
             break;
           }
    }
  else
    {

      // fast canonicalize
      temp = *this;
      for (j=0; j<2; j++)
        array[Perm.class_mu_1_NODE[j]+0] = temp[j+1];
    }
}
void mu_1__type_1::SimpleLimit(PermSet& Perm){}
void mu_1__type_1::ArrayLimit(PermSet& Perm)
{
  // indexes
  int i,j,k,z;
  // sorting
  int count_mu_1_NODE;
  int compare;
  static mu_1_MSG value[2];
  // limit
  bool exists;
  bool split;
  bool goodset_mu_1_NODE[2];
  bool pos_mu_1_NODE[2][2];
  // sorting mu_1_NODE
  // only if there is more than 1 permutation in class
  if (Perm.MTO_class_mu_1_NODE())
    {
      for (i=0; i<2; i++)
        for (j=0; j<2; j++)
          pos_mu_1_NODE[i][j]=FALSE;
      count_mu_1_NODE = 0;
      for (i=0; i<2; i++)
        {
          for (j=0; j<count_mu_1_NODE; j++)
            {
              compare = CompareWeight(value[j],(*this)[i+1]);
              if (compare==0)
                {
                  pos_mu_1_NODE[j][i]= TRUE;
                  break;
                }
              else if (compare>0)
                {
                  for (k=count_mu_1_NODE; k>j; k--)
                    {
                      value[k] = value[k-1];
                      for (z=0; z<2; z++)
                        pos_mu_1_NODE[k][z] = pos_mu_1_NODE[k-1][z];
                    }
                  value[j] = (*this)[i+1];
                  for (z=0; z<2; z++)
                    pos_mu_1_NODE[j][z] = FALSE;
                  pos_mu_1_NODE[j][i] = TRUE;
                  count_mu_1_NODE++;
                  break;
                }
            }
          if (j==count_mu_1_NODE)
            {
              value[j] = (*this)[i+1];
              for (z=0; z<2; z++)
                pos_mu_1_NODE[j][z] = FALSE;
              pos_mu_1_NODE[j][i] = TRUE;
              count_mu_1_NODE++;
            }
        }
    }
  // if there is more than 1 permutation in class
  if (Perm.MTO_class_mu_1_NODE() && count_mu_1_NODE>1)
    {
      // limit
      for (j=0; j<2; j++) // class priority
        {
          for (i=0; i<count_mu_1_NODE; i++) // for value priority
            {
              exists = FALSE;
              for (k=0; k<2; k++) // step through class
                goodset_mu_1_NODE[k] = FALSE;
              for (k=0; k<2; k++) // step through class
                if (pos_mu_1_NODE[i][k] && Perm.class_mu_1_NODE[k] == j)
                  {
                    exists = TRUE;
                    goodset_mu_1_NODE[k] = TRUE;
                    pos_mu_1_NODE[i][k] = FALSE;
                  }
              if (exists)
                {
                  split=FALSE;
                  for (k=0; k<2; k++)
                    if ( Perm.class_mu_1_NODE[k] == j && !goodset_mu_1_NODE[k] ) 
                      split= TRUE;
                  if (split)
                    {
                      for (k=0; k<2; k++)
                        if (Perm.class_mu_1_NODE[k]>j
                            || ( Perm.class_mu_1_NODE[k] == j && !goodset_mu_1_NODE[k] ) )
                          Perm.class_mu_1_NODE[k]++;
                      Perm.undefined_class_mu_1_NODE++;
                    }
                }
            }
        }
    }
}
void mu_1__type_1::Limit(PermSet& Perm){}
void mu_1__type_1::MultisetLimit(PermSet& Perm)
{ Error.Error("Internal: calling MultisetLimit for scalarset array.\n"); };
void mu_1__type_2::Permute(PermSet& Perm, int i)
{
  static mu_1__type_2 temp("Permute_mu_1__type_2",-1);
  int j;
  for (j=0; j<2; j++)
    array[j].Permute(Perm, i);
  temp = *this;
  for (j=1; j<=2; j++)
    (*this)[j] = temp[Perm.revperm_mu_1_NODE[Perm.in_mu_1_NODE[i]][j-1]];};
void mu_1__type_2::SimpleCanonicalize(PermSet& Perm)
{ Error.Error("Internal: Simple Canonicalization of Scalarset Array\n"); };
void mu_1__type_2::Canonicalize(PermSet& Perm)
{
  // indexes
  int i,j,k,z;
  // sorting
  int count_mu_1_NODE;
  int compare;
  static mu_1_MSG value[2];
  // limit
  bool exists;
  bool split;
  bool goodset_mu_1_NODE[2];
  bool pos_mu_1_NODE[2][2];
  // range mapping
  int start;
  int class_size;
  int size_mu_1_NODE[2];
  int start_mu_1_NODE[2];
  // canonicalization
  static mu_1__type_2 temp;
  // sorting mu_1_NODE
  // only if there is more than 1 permutation in class
  if (Perm.MTO_class_mu_1_NODE())
    {
      for (i=0; i<2; i++)
        for (j=0; j<2; j++)
          pos_mu_1_NODE[i][j]=FALSE;
      count_mu_1_NODE = 0;
      for (i=0; i<2; i++)
        {
          for (j=0; j<count_mu_1_NODE; j++)
            {
              compare = CompareWeight(value[j],(*this)[i+1]);
              if (compare==0)
                {
                  pos_mu_1_NODE[j][i]= TRUE;
                  break;
                }
              else if (compare>0)
                {
                  for (k=count_mu_1_NODE; k>j; k--)
                    {
                      value[k] = value[k-1];
                      for (z=0; z<2; z++)
                        pos_mu_1_NODE[k][z] = pos_mu_1_NODE[k-1][z];
                    }
                  value[j] = (*this)[i+1];
                  for (z=0; z<2; z++)
                    pos_mu_1_NODE[j][z] = FALSE;
                  pos_mu_1_NODE[j][i] = TRUE;
                  count_mu_1_NODE++;
                  break;
                }
            }
          if (j==count_mu_1_NODE)
            {
              value[j] = (*this)[i+1];
              for (z=0; z<2; z++)
                pos_mu_1_NODE[j][z] = FALSE;
              pos_mu_1_NODE[j][i] = TRUE;
              count_mu_1_NODE++;
            }
        }
    }
  // if there is more than 1 permutation in class
  if (Perm.MTO_class_mu_1_NODE() && count_mu_1_NODE>1)
    {
      // limit
      for (j=0; j<2; j++) // class priority
        {
          for (i=0; i<count_mu_1_NODE; i++) // for value priority
            {
              exists = FALSE;
              for (k=0; k<2; k++) // step through class
                goodset_mu_1_NODE[k] = FALSE;
              for (k=0; k<2; k++) // step through class
                if (pos_mu_1_NODE[i][k] && Perm.class_mu_1_NODE[k] == j)
                  {
                    exists = TRUE;
                    goodset_mu_1_NODE[k] = TRUE;
                    pos_mu_1_NODE[i][k] = FALSE;
                  }
              if (exists)
                {
                  split=FALSE;
                  for (k=0; k<2; k++)
                    if ( Perm.class_mu_1_NODE[k] == j && !goodset_mu_1_NODE[k] ) 
                      split= TRUE;
                  if (split)
                    {
                      for (k=0; k<2; k++)
                        if (Perm.class_mu_1_NODE[k]>j
                            || ( Perm.class_mu_1_NODE[k] == j && !goodset_mu_1_NODE[k] ) )
                          Perm.class_mu_1_NODE[k]++;
                      Perm.undefined_class_mu_1_NODE++;
                    }
                }
            }
        }
    }
  if (Perm.MTO_class_mu_1_NODE())
    {

      // setup range for maping
      start = 0;
      for (j=0; j<=Perm.undefined_class_mu_1_NODE; j++) // class number
        {
          class_size = 0;
          for (k=0; k<2; k++) // step through class[k]
            if (Perm.class_mu_1_NODE[k]==j)
              class_size++;
          for (k=0; k<2; k++) // step through class[k]
            if (Perm.class_mu_1_NODE[k]==j)
              {
                size_mu_1_NODE[k] = class_size;
                start_mu_1_NODE[k] = start;
              }
          start+=class_size;
        }

      // canonicalize
      temp = *this;
      for (i=0; i<2; i++)
        for (j=0; j<2; j++)
         if (i >=start_mu_1_NODE[j] 
             && i < start_mu_1_NODE[j] + size_mu_1_NODE[j])
           {
             array[i+0] = temp[j+1];
             break;
           }
    }
  else
    {

      // fast canonicalize
      temp = *this;
      for (j=0; j<2; j++)
        array[Perm.class_mu_1_NODE[j]+0] = temp[j+1];
    }
}
void mu_1__type_2::SimpleLimit(PermSet& Perm){}
void mu_1__type_2::ArrayLimit(PermSet& Perm)
{
  // indexes
  int i,j,k,z;
  // sorting
  int count_mu_1_NODE;
  int compare;
  static mu_1_MSG value[2];
  // limit
  bool exists;
  bool split;
  bool goodset_mu_1_NODE[2];
  bool pos_mu_1_NODE[2][2];
  // sorting mu_1_NODE
  // only if there is more than 1 permutation in class
  if (Perm.MTO_class_mu_1_NODE())
    {
      for (i=0; i<2; i++)
        for (j=0; j<2; j++)
          pos_mu_1_NODE[i][j]=FALSE;
      count_mu_1_NODE = 0;
      for (i=0; i<2; i++)
        {
          for (j=0; j<count_mu_1_NODE; j++)
            {
              compare = CompareWeight(value[j],(*this)[i+1]);
              if (compare==0)
                {
                  pos_mu_1_NODE[j][i]= TRUE;
                  break;
                }
              else if (compare>0)
                {
                  for (k=count_mu_1_NODE; k>j; k--)
                    {
                      value[k] = value[k-1];
                      for (z=0; z<2; z++)
                        pos_mu_1_NODE[k][z] = pos_mu_1_NODE[k-1][z];
                    }
                  value[j] = (*this)[i+1];
                  for (z=0; z<2; z++)
                    pos_mu_1_NODE[j][z] = FALSE;
                  pos_mu_1_NODE[j][i] = TRUE;
                  count_mu_1_NODE++;
                  break;
                }
            }
          if (j==count_mu_1_NODE)
            {
              value[j] = (*this)[i+1];
              for (z=0; z<2; z++)
                pos_mu_1_NODE[j][z] = FALSE;
              pos_mu_1_NODE[j][i] = TRUE;
              count_mu_1_NODE++;
            }
        }
    }
  // if there is more than 1 permutation in class
  if (Perm.MTO_class_mu_1_NODE() && count_mu_1_NODE>1)
    {
      // limit
      for (j=0; j<2; j++) // class priority
        {
          for (i=0; i<count_mu_1_NODE; i++) // for value priority
            {
              exists = FALSE;
              for (k=0; k<2; k++) // step through class
                goodset_mu_1_NODE[k] = FALSE;
              for (k=0; k<2; k++) // step through class
                if (pos_mu_1_NODE[i][k] && Perm.class_mu_1_NODE[k] == j)
                  {
                    exists = TRUE;
                    goodset_mu_1_NODE[k] = TRUE;
                    pos_mu_1_NODE[i][k] = FALSE;
                  }
              if (exists)
                {
                  split=FALSE;
                  for (k=0; k<2; k++)
                    if ( Perm.class_mu_1_NODE[k] == j && !goodset_mu_1_NODE[k] ) 
                      split= TRUE;
                  if (split)
                    {
                      for (k=0; k<2; k++)
                        if (Perm.class_mu_1_NODE[k]>j
                            || ( Perm.class_mu_1_NODE[k] == j && !goodset_mu_1_NODE[k] ) )
                          Perm.class_mu_1_NODE[k]++;
                      Perm.undefined_class_mu_1_NODE++;
                    }
                }
            }
        }
    }
}
void mu_1__type_2::Limit(PermSet& Perm){}
void mu_1__type_2::MultisetLimit(PermSet& Perm)
{ Error.Error("Internal: calling MultisetLimit for scalarset array.\n"); };
void mu_1__type_3::Permute(PermSet& Perm, int i)
{
  static mu_1__type_3 temp("Permute_mu_1__type_3",-1);
  int j;
  for (j=0; j<2; j++)
    array[j].Permute(Perm, i);
  temp = *this;
  for (j=1; j<=2; j++)
    (*this)[j] = temp[Perm.revperm_mu_1_NODE[Perm.in_mu_1_NODE[i]][j-1]];};
void mu_1__type_3::SimpleCanonicalize(PermSet& Perm)
{ Error.Error("Internal: Simple Canonicalization of Scalarset Array\n"); };
void mu_1__type_3::Canonicalize(PermSet& Perm)
{
  // indexes
  int i,j,k,z;
  // sorting
  int count_mu_1_NODE;
  int compare;
  static mu_1_MSG value[2];
  // limit
  bool exists;
  bool split;
  bool goodset_mu_1_NODE[2];
  bool pos_mu_1_NODE[2][2];
  // range mapping
  int start;
  int class_size;
  int size_mu_1_NODE[2];
  int start_mu_1_NODE[2];
  // canonicalization
  static mu_1__type_3 temp;
  // sorting mu_1_NODE
  // only if there is more than 1 permutation in class
  if (Perm.MTO_class_mu_1_NODE())
    {
      for (i=0; i<2; i++)
        for (j=0; j<2; j++)
          pos_mu_1_NODE[i][j]=FALSE;
      count_mu_1_NODE = 0;
      for (i=0; i<2; i++)
        {
          for (j=0; j<count_mu_1_NODE; j++)
            {
              compare = CompareWeight(value[j],(*this)[i+1]);
              if (compare==0)
                {
                  pos_mu_1_NODE[j][i]= TRUE;
                  break;
                }
              else if (compare>0)
                {
                  for (k=count_mu_1_NODE; k>j; k--)
                    {
                      value[k] = value[k-1];
                      for (z=0; z<2; z++)
                        pos_mu_1_NODE[k][z] = pos_mu_1_NODE[k-1][z];
                    }
                  value[j] = (*this)[i+1];
                  for (z=0; z<2; z++)
                    pos_mu_1_NODE[j][z] = FALSE;
                  pos_mu_1_NODE[j][i] = TRUE;
                  count_mu_1_NODE++;
                  break;
                }
            }
          if (j==count_mu_1_NODE)
            {
              value[j] = (*this)[i+1];
              for (z=0; z<2; z++)
                pos_mu_1_NODE[j][z] = FALSE;
              pos_mu_1_NODE[j][i] = TRUE;
              count_mu_1_NODE++;
            }
        }
    }
  // if there is more than 1 permutation in class
  if (Perm.MTO_class_mu_1_NODE() && count_mu_1_NODE>1)
    {
      // limit
      for (j=0; j<2; j++) // class priority
        {
          for (i=0; i<count_mu_1_NODE; i++) // for value priority
            {
              exists = FALSE;
              for (k=0; k<2; k++) // step through class
                goodset_mu_1_NODE[k] = FALSE;
              for (k=0; k<2; k++) // step through class
                if (pos_mu_1_NODE[i][k] && Perm.class_mu_1_NODE[k] == j)
                  {
                    exists = TRUE;
                    goodset_mu_1_NODE[k] = TRUE;
                    pos_mu_1_NODE[i][k] = FALSE;
                  }
              if (exists)
                {
                  split=FALSE;
                  for (k=0; k<2; k++)
                    if ( Perm.class_mu_1_NODE[k] == j && !goodset_mu_1_NODE[k] ) 
                      split= TRUE;
                  if (split)
                    {
                      for (k=0; k<2; k++)
                        if (Perm.class_mu_1_NODE[k]>j
                            || ( Perm.class_mu_1_NODE[k] == j && !goodset_mu_1_NODE[k] ) )
                          Perm.class_mu_1_NODE[k]++;
                      Perm.undefined_class_mu_1_NODE++;
                    }
                }
            }
        }
    }
  if (Perm.MTO_class_mu_1_NODE())
    {

      // setup range for maping
      start = 0;
      for (j=0; j<=Perm.undefined_class_mu_1_NODE; j++) // class number
        {
          class_size = 0;
          for (k=0; k<2; k++) // step through class[k]
            if (Perm.class_mu_1_NODE[k]==j)
              class_size++;
          for (k=0; k<2; k++) // step through class[k]
            if (Perm.class_mu_1_NODE[k]==j)
              {
                size_mu_1_NODE[k] = class_size;
                start_mu_1_NODE[k] = start;
              }
          start+=class_size;
        }

      // canonicalize
      temp = *this;
      for (i=0; i<2; i++)
        for (j=0; j<2; j++)
         if (i >=start_mu_1_NODE[j] 
             && i < start_mu_1_NODE[j] + size_mu_1_NODE[j])
           {
             array[i+0] = temp[j+1];
             break;
           }
    }
  else
    {

      // fast canonicalize
      temp = *this;
      for (j=0; j<2; j++)
        array[Perm.class_mu_1_NODE[j]+0] = temp[j+1];
    }
}
void mu_1__type_3::SimpleLimit(PermSet& Perm){}
void mu_1__type_3::ArrayLimit(PermSet& Perm)
{
  // indexes
  int i,j,k,z;
  // sorting
  int count_mu_1_NODE;
  int compare;
  static mu_1_MSG value[2];
  // limit
  bool exists;
  bool split;
  bool goodset_mu_1_NODE[2];
  bool pos_mu_1_NODE[2][2];
  // sorting mu_1_NODE
  // only if there is more than 1 permutation in class
  if (Perm.MTO_class_mu_1_NODE())
    {
      for (i=0; i<2; i++)
        for (j=0; j<2; j++)
          pos_mu_1_NODE[i][j]=FALSE;
      count_mu_1_NODE = 0;
      for (i=0; i<2; i++)
        {
          for (j=0; j<count_mu_1_NODE; j++)
            {
              compare = CompareWeight(value[j],(*this)[i+1]);
              if (compare==0)
                {
                  pos_mu_1_NODE[j][i]= TRUE;
                  break;
                }
              else if (compare>0)
                {
                  for (k=count_mu_1_NODE; k>j; k--)
                    {
                      value[k] = value[k-1];
                      for (z=0; z<2; z++)
                        pos_mu_1_NODE[k][z] = pos_mu_1_NODE[k-1][z];
                    }
                  value[j] = (*this)[i+1];
                  for (z=0; z<2; z++)
                    pos_mu_1_NODE[j][z] = FALSE;
                  pos_mu_1_NODE[j][i] = TRUE;
                  count_mu_1_NODE++;
                  break;
                }
            }
          if (j==count_mu_1_NODE)
            {
              value[j] = (*this)[i+1];
              for (z=0; z<2; z++)
                pos_mu_1_NODE[j][z] = FALSE;
              pos_mu_1_NODE[j][i] = TRUE;
              count_mu_1_NODE++;
            }
        }
    }
  // if there is more than 1 permutation in class
  if (Perm.MTO_class_mu_1_NODE() && count_mu_1_NODE>1)
    {
      // limit
      for (j=0; j<2; j++) // class priority
        {
          for (i=0; i<count_mu_1_NODE; i++) // for value priority
            {
              exists = FALSE;
              for (k=0; k<2; k++) // step through class
                goodset_mu_1_NODE[k] = FALSE;
              for (k=0; k<2; k++) // step through class
                if (pos_mu_1_NODE[i][k] && Perm.class_mu_1_NODE[k] == j)
                  {
                    exists = TRUE;
                    goodset_mu_1_NODE[k] = TRUE;
                    pos_mu_1_NODE[i][k] = FALSE;
                  }
              if (exists)
                {
                  split=FALSE;
                  for (k=0; k<2; k++)
                    if ( Perm.class_mu_1_NODE[k] == j && !goodset_mu_1_NODE[k] ) 
                      split= TRUE;
                  if (split)
                    {
                      for (k=0; k<2; k++)
                        if (Perm.class_mu_1_NODE[k]>j
                            || ( Perm.class_mu_1_NODE[k] == j && !goodset_mu_1_NODE[k] ) )
                          Perm.class_mu_1_NODE[k]++;
                      Perm.undefined_class_mu_1_NODE++;
                    }
                }
            }
        }
    }
}
void mu_1__type_3::Limit(PermSet& Perm){}
void mu_1__type_3::MultisetLimit(PermSet& Perm)
{ Error.Error("Internal: calling MultisetLimit for scalarset array.\n"); };
void mu_1__type_4::Permute(PermSet& Perm, int i)
{
  static mu_1__type_4 temp("Permute_mu_1__type_4",-1);
  int j;
  for (j=0; j<2; j++)
    array[j].Permute(Perm, i);
  temp = *this;
  for (j=1; j<=2; j++)
     (*this)[j].value(temp[Perm.revperm_mu_1_NODE[Perm.in_mu_1_NODE[i]][j-1]].value());};
void mu_1__type_4::SimpleCanonicalize(PermSet& Perm)
{ Error.Error("Internal: Simple Canonicalization of Scalarset Array\n"); };
void mu_1__type_4::Canonicalize(PermSet& Perm)
{
  // indexes
  int i,j,k,z;
  // sorting
  int count_mu_1_NODE;
  int compare;
  static mu_0_boolean value[2];
  // limit
  bool exists;
  bool split;
  bool goodset_mu_1_NODE[2];
  bool pos_mu_1_NODE[2][2];
  // range mapping
  int start;
  int class_size;
  int size_mu_1_NODE[2];
  int start_mu_1_NODE[2];
  // canonicalization
  static mu_1__type_4 temp;
  // sorting mu_1_NODE
  // only if there is more than 1 permutation in class
  if (Perm.MTO_class_mu_1_NODE())
    {
      for (i=0; i<2; i++)
        for (j=0; j<2; j++)
          pos_mu_1_NODE[i][j]=FALSE;
      count_mu_1_NODE = 0;
      for (i=0; i<2; i++)
        {
          for (j=0; j<count_mu_1_NODE; j++)
            {
              compare = CompareWeight(value[j],(*this)[i+1]);
              if (compare==0)
                {
                  pos_mu_1_NODE[j][i]= TRUE;
                  break;
                }
              else if (compare>0)
                {
                  for (k=count_mu_1_NODE; k>j; k--)
                    {
                      value[k].value(value[k-1].value());
                      for (z=0; z<2; z++)
                        pos_mu_1_NODE[k][z] = pos_mu_1_NODE[k-1][z];
                    }
                  value[j].value((*this)[i+1].value());
                  for (z=0; z<2; z++)
                    pos_mu_1_NODE[j][z] = FALSE;
                  pos_mu_1_NODE[j][i] = TRUE;
                  count_mu_1_NODE++;
                  break;
                }
            }
          if (j==count_mu_1_NODE)
            {
                value[j].value((*this)[i+1].value());
              for (z=0; z<2; z++)
                pos_mu_1_NODE[j][z] = FALSE;
              pos_mu_1_NODE[j][i] = TRUE;
              count_mu_1_NODE++;
            }
        }
    }
  // if there is more than 1 permutation in class
  if (Perm.MTO_class_mu_1_NODE() && count_mu_1_NODE>1)
    {
      // limit
      for (j=0; j<2; j++) // class priority
        {
          for (i=0; i<count_mu_1_NODE; i++) // for value priority
            {
              exists = FALSE;
              for (k=0; k<2; k++) // step through class
                goodset_mu_1_NODE[k] = FALSE;
              for (k=0; k<2; k++) // step through class
                if (pos_mu_1_NODE[i][k] && Perm.class_mu_1_NODE[k] == j)
                  {
                    exists = TRUE;
                    goodset_mu_1_NODE[k] = TRUE;
                    pos_mu_1_NODE[i][k] = FALSE;
                  }
              if (exists)
                {
                  split=FALSE;
                  for (k=0; k<2; k++)
                    if ( Perm.class_mu_1_NODE[k] == j && !goodset_mu_1_NODE[k] ) 
                      split= TRUE;
                  if (split)
                    {
                      for (k=0; k<2; k++)
                        if (Perm.class_mu_1_NODE[k]>j
                            || ( Perm.class_mu_1_NODE[k] == j && !goodset_mu_1_NODE[k] ) )
                          Perm.class_mu_1_NODE[k]++;
                      Perm.undefined_class_mu_1_NODE++;
                    }
                }
            }
        }
    }
  if (Perm.MTO_class_mu_1_NODE())
    {

      // setup range for maping
      start = 0;
      for (j=0; j<=Perm.undefined_class_mu_1_NODE; j++) // class number
        {
          class_size = 0;
          for (k=0; k<2; k++) // step through class[k]
            if (Perm.class_mu_1_NODE[k]==j)
              class_size++;
          for (k=0; k<2; k++) // step through class[k]
            if (Perm.class_mu_1_NODE[k]==j)
              {
                size_mu_1_NODE[k] = class_size;
                start_mu_1_NODE[k] = start;
              }
          start+=class_size;
        }

      // canonicalize
      temp = *this;
      for (i=0; i<2; i++)
        for (j=0; j<2; j++)
         if (i >=start_mu_1_NODE[j] 
             && i < start_mu_1_NODE[j] + size_mu_1_NODE[j])
           {
             array[i+0].value(temp[j+1].value());
             break;
           }
    }
  else
    {

      // fast canonicalize
      temp = *this;
      for (j=0; j<2; j++)
        array[Perm.class_mu_1_NODE[j]+0].value(temp[j+1].value());
    }
}
void mu_1__type_4::SimpleLimit(PermSet& Perm){}
void mu_1__type_4::ArrayLimit(PermSet& Perm)
{
  // indexes
  int i,j,k,z;
  // sorting
  int count_mu_1_NODE;
  int compare;
  static mu_0_boolean value[2];
  // limit
  bool exists;
  bool split;
  bool goodset_mu_1_NODE[2];
  bool pos_mu_1_NODE[2][2];
  // sorting mu_1_NODE
  // only if there is more than 1 permutation in class
  if (Perm.MTO_class_mu_1_NODE())
    {
      for (i=0; i<2; i++)
        for (j=0; j<2; j++)
          pos_mu_1_NODE[i][j]=FALSE;
      count_mu_1_NODE = 0;
      for (i=0; i<2; i++)
        {
          for (j=0; j<count_mu_1_NODE; j++)
            {
              compare = CompareWeight(value[j],(*this)[i+1]);
              if (compare==0)
                {
                  pos_mu_1_NODE[j][i]= TRUE;
                  break;
                }
              else if (compare>0)
                {
                  for (k=count_mu_1_NODE; k>j; k--)
                    {
                      value[k].value(value[k-1].value());
                      for (z=0; z<2; z++)
                        pos_mu_1_NODE[k][z] = pos_mu_1_NODE[k-1][z];
                    }
                  value[j].value((*this)[i+1].value());
                  for (z=0; z<2; z++)
                    pos_mu_1_NODE[j][z] = FALSE;
                  pos_mu_1_NODE[j][i] = TRUE;
                  count_mu_1_NODE++;
                  break;
                }
            }
          if (j==count_mu_1_NODE)
            {
                value[j].value((*this)[i+1].value());
              for (z=0; z<2; z++)
                pos_mu_1_NODE[j][z] = FALSE;
              pos_mu_1_NODE[j][i] = TRUE;
              count_mu_1_NODE++;
            }
        }
    }
  // if there is more than 1 permutation in class
  if (Perm.MTO_class_mu_1_NODE() && count_mu_1_NODE>1)
    {
      // limit
      for (j=0; j<2; j++) // class priority
        {
          for (i=0; i<count_mu_1_NODE; i++) // for value priority
            {
              exists = FALSE;
              for (k=0; k<2; k++) // step through class
                goodset_mu_1_NODE[k] = FALSE;
              for (k=0; k<2; k++) // step through class
                if (pos_mu_1_NODE[i][k] && Perm.class_mu_1_NODE[k] == j)
                  {
                    exists = TRUE;
                    goodset_mu_1_NODE[k] = TRUE;
                    pos_mu_1_NODE[i][k] = FALSE;
                  }
              if (exists)
                {
                  split=FALSE;
                  for (k=0; k<2; k++)
                    if ( Perm.class_mu_1_NODE[k] == j && !goodset_mu_1_NODE[k] ) 
                      split= TRUE;
                  if (split)
                    {
                      for (k=0; k<2; k++)
                        if (Perm.class_mu_1_NODE[k]>j
                            || ( Perm.class_mu_1_NODE[k] == j && !goodset_mu_1_NODE[k] ) )
                          Perm.class_mu_1_NODE[k]++;
                      Perm.undefined_class_mu_1_NODE++;
                    }
                }
            }
        }
    }
}
void mu_1__type_4::Limit(PermSet& Perm){}
void mu_1__type_4::MultisetLimit(PermSet& Perm)
{ Error.Error("Internal: calling MultisetLimit for scalarset array.\n"); };
void mu_1__type_5::Permute(PermSet& Perm, int i)
{
  static mu_1__type_5 temp("Permute_mu_1__type_5",-1);
  int j;
  for (j=0; j<2; j++)
    array[j].Permute(Perm, i);
  temp = *this;
  for (j=1; j<=2; j++)
     (*this)[j].value(temp[Perm.revperm_mu_1_NODE[Perm.in_mu_1_NODE[i]][j-1]].value());};
void mu_1__type_5::SimpleCanonicalize(PermSet& Perm)
{ Error.Error("Internal: Simple Canonicalization of Scalarset Array\n"); };
void mu_1__type_5::Canonicalize(PermSet& Perm)
{
  // indexes
  int i,j,k,z;
  // sorting
  int count_mu_1_NODE;
  int compare;
  static mu_0_boolean value[2];
  // limit
  bool exists;
  bool split;
  bool goodset_mu_1_NODE[2];
  bool pos_mu_1_NODE[2][2];
  // range mapping
  int start;
  int class_size;
  int size_mu_1_NODE[2];
  int start_mu_1_NODE[2];
  // canonicalization
  static mu_1__type_5 temp;
  // sorting mu_1_NODE
  // only if there is more than 1 permutation in class
  if (Perm.MTO_class_mu_1_NODE())
    {
      for (i=0; i<2; i++)
        for (j=0; j<2; j++)
          pos_mu_1_NODE[i][j]=FALSE;
      count_mu_1_NODE = 0;
      for (i=0; i<2; i++)
        {
          for (j=0; j<count_mu_1_NODE; j++)
            {
              compare = CompareWeight(value[j],(*this)[i+1]);
              if (compare==0)
                {
                  pos_mu_1_NODE[j][i]= TRUE;
                  break;
                }
              else if (compare>0)
                {
                  for (k=count_mu_1_NODE; k>j; k--)
                    {
                      value[k].value(value[k-1].value());
                      for (z=0; z<2; z++)
                        pos_mu_1_NODE[k][z] = pos_mu_1_NODE[k-1][z];
                    }
                  value[j].value((*this)[i+1].value());
                  for (z=0; z<2; z++)
                    pos_mu_1_NODE[j][z] = FALSE;
                  pos_mu_1_NODE[j][i] = TRUE;
                  count_mu_1_NODE++;
                  break;
                }
            }
          if (j==count_mu_1_NODE)
            {
                value[j].value((*this)[i+1].value());
              for (z=0; z<2; z++)
                pos_mu_1_NODE[j][z] = FALSE;
              pos_mu_1_NODE[j][i] = TRUE;
              count_mu_1_NODE++;
            }
        }
    }
  // if there is more than 1 permutation in class
  if (Perm.MTO_class_mu_1_NODE() && count_mu_1_NODE>1)
    {
      // limit
      for (j=0; j<2; j++) // class priority
        {
          for (i=0; i<count_mu_1_NODE; i++) // for value priority
            {
              exists = FALSE;
              for (k=0; k<2; k++) // step through class
                goodset_mu_1_NODE[k] = FALSE;
              for (k=0; k<2; k++) // step through class
                if (pos_mu_1_NODE[i][k] && Perm.class_mu_1_NODE[k] == j)
                  {
                    exists = TRUE;
                    goodset_mu_1_NODE[k] = TRUE;
                    pos_mu_1_NODE[i][k] = FALSE;
                  }
              if (exists)
                {
                  split=FALSE;
                  for (k=0; k<2; k++)
                    if ( Perm.class_mu_1_NODE[k] == j && !goodset_mu_1_NODE[k] ) 
                      split= TRUE;
                  if (split)
                    {
                      for (k=0; k<2; k++)
                        if (Perm.class_mu_1_NODE[k]>j
                            || ( Perm.class_mu_1_NODE[k] == j && !goodset_mu_1_NODE[k] ) )
                          Perm.class_mu_1_NODE[k]++;
                      Perm.undefined_class_mu_1_NODE++;
                    }
                }
            }
        }
    }
  if (Perm.MTO_class_mu_1_NODE())
    {

      // setup range for maping
      start = 0;
      for (j=0; j<=Perm.undefined_class_mu_1_NODE; j++) // class number
        {
          class_size = 0;
          for (k=0; k<2; k++) // step through class[k]
            if (Perm.class_mu_1_NODE[k]==j)
              class_size++;
          for (k=0; k<2; k++) // step through class[k]
            if (Perm.class_mu_1_NODE[k]==j)
              {
                size_mu_1_NODE[k] = class_size;
                start_mu_1_NODE[k] = start;
              }
          start+=class_size;
        }

      // canonicalize
      temp = *this;
      for (i=0; i<2; i++)
        for (j=0; j<2; j++)
         if (i >=start_mu_1_NODE[j] 
             && i < start_mu_1_NODE[j] + size_mu_1_NODE[j])
           {
             array[i+0].value(temp[j+1].value());
             break;
           }
    }
  else
    {

      // fast canonicalize
      temp = *this;
      for (j=0; j<2; j++)
        array[Perm.class_mu_1_NODE[j]+0].value(temp[j+1].value());
    }
}
void mu_1__type_5::SimpleLimit(PermSet& Perm){}
void mu_1__type_5::ArrayLimit(PermSet& Perm)
{
  // indexes
  int i,j,k,z;
  // sorting
  int count_mu_1_NODE;
  int compare;
  static mu_0_boolean value[2];
  // limit
  bool exists;
  bool split;
  bool goodset_mu_1_NODE[2];
  bool pos_mu_1_NODE[2][2];
  // sorting mu_1_NODE
  // only if there is more than 1 permutation in class
  if (Perm.MTO_class_mu_1_NODE())
    {
      for (i=0; i<2; i++)
        for (j=0; j<2; j++)
          pos_mu_1_NODE[i][j]=FALSE;
      count_mu_1_NODE = 0;
      for (i=0; i<2; i++)
        {
          for (j=0; j<count_mu_1_NODE; j++)
            {
              compare = CompareWeight(value[j],(*this)[i+1]);
              if (compare==0)
                {
                  pos_mu_1_NODE[j][i]= TRUE;
                  break;
                }
              else if (compare>0)
                {
                  for (k=count_mu_1_NODE; k>j; k--)
                    {
                      value[k].value(value[k-1].value());
                      for (z=0; z<2; z++)
                        pos_mu_1_NODE[k][z] = pos_mu_1_NODE[k-1][z];
                    }
                  value[j].value((*this)[i+1].value());
                  for (z=0; z<2; z++)
                    pos_mu_1_NODE[j][z] = FALSE;
                  pos_mu_1_NODE[j][i] = TRUE;
                  count_mu_1_NODE++;
                  break;
                }
            }
          if (j==count_mu_1_NODE)
            {
                value[j].value((*this)[i+1].value());
              for (z=0; z<2; z++)
                pos_mu_1_NODE[j][z] = FALSE;
              pos_mu_1_NODE[j][i] = TRUE;
              count_mu_1_NODE++;
            }
        }
    }
  // if there is more than 1 permutation in class
  if (Perm.MTO_class_mu_1_NODE() && count_mu_1_NODE>1)
    {
      // limit
      for (j=0; j<2; j++) // class priority
        {
          for (i=0; i<count_mu_1_NODE; i++) // for value priority
            {
              exists = FALSE;
              for (k=0; k<2; k++) // step through class
                goodset_mu_1_NODE[k] = FALSE;
              for (k=0; k<2; k++) // step through class
                if (pos_mu_1_NODE[i][k] && Perm.class_mu_1_NODE[k] == j)
                  {
                    exists = TRUE;
                    goodset_mu_1_NODE[k] = TRUE;
                    pos_mu_1_NODE[i][k] = FALSE;
                  }
              if (exists)
                {
                  split=FALSE;
                  for (k=0; k<2; k++)
                    if ( Perm.class_mu_1_NODE[k] == j && !goodset_mu_1_NODE[k] ) 
                      split= TRUE;
                  if (split)
                    {
                      for (k=0; k<2; k++)
                        if (Perm.class_mu_1_NODE[k]>j
                            || ( Perm.class_mu_1_NODE[k] == j && !goodset_mu_1_NODE[k] ) )
                          Perm.class_mu_1_NODE[k]++;
                      Perm.undefined_class_mu_1_NODE++;
                    }
                }
            }
        }
    }
}
void mu_1__type_5::Limit(PermSet& Perm){}
void mu_1__type_5::MultisetLimit(PermSet& Perm)
{ Error.Error("Internal: calling MultisetLimit for scalarset array.\n"); };

/********************
 Auxiliary function for error trace printing
 ********************/
bool match(state* ns, StatePtr p)
{
  int i;
  static PermSet Perm;
  static state temp;
  StateCopy(&temp, ns);
  if (args->symmetry_reduction.value)
    {
      if (  args->sym_alg.mode == argsym_alg::Exhaustive_Fast_Canonicalize) {
        Perm.ResetToExplicit();
        for (i=0; i<Perm.count; i++)
          if (Perm.In(i))
            {
              if (ns != workingstate)
                  StateCopy(workingstate, ns);
              
              mu_CurCmd.Permute(Perm,i);
              if (args->multiset_reduction.value)
                mu_CurCmd.MultisetSort();
              mu_ExGntd.Permute(Perm,i);
              if (args->multiset_reduction.value)
                mu_ExGntd.MultisetSort();
              mu_CurPtr.Permute(Perm,i);
              if (args->multiset_reduction.value)
                mu_CurPtr.MultisetSort();
              mu_ShrSet.Permute(Perm,i);
              if (args->multiset_reduction.value)
                mu_ShrSet.MultisetSort();
              mu_InvSet.Permute(Perm,i);
              if (args->multiset_reduction.value)
                mu_InvSet.MultisetSort();
              mu_Chan3.Permute(Perm,i);
              if (args->multiset_reduction.value)
                mu_Chan3.MultisetSort();
              mu_Chan2.Permute(Perm,i);
              if (args->multiset_reduction.value)
                mu_Chan2.MultisetSort();
              mu_Chan1.Permute(Perm,i);
              if (args->multiset_reduction.value)
                mu_Chan1.MultisetSort();
              mu_Cache.Permute(Perm,i);
              if (args->multiset_reduction.value)
                mu_Cache.MultisetSort();
            if (p.compare(workingstate)) {
              StateCopy(workingstate,&temp); return TRUE; }
          }
        StateCopy(workingstate,&temp);
        return FALSE;
      }
      else {
        Perm.ResetToSimple();
        Perm.SimpleToOne();
        if (ns != workingstate)
          StateCopy(workingstate, ns);

          mu_CurCmd.Permute(Perm,0);
          if (args->multiset_reduction.value)
            mu_CurCmd.MultisetSort();
          mu_ExGntd.Permute(Perm,0);
          if (args->multiset_reduction.value)
            mu_ExGntd.MultisetSort();
          mu_CurPtr.Permute(Perm,0);
          if (args->multiset_reduction.value)
            mu_CurPtr.MultisetSort();
          mu_ShrSet.Permute(Perm,0);
          if (args->multiset_reduction.value)
            mu_ShrSet.MultisetSort();
          mu_InvSet.Permute(Perm,0);
          if (args->multiset_reduction.value)
            mu_InvSet.MultisetSort();
          mu_Chan3.Permute(Perm,0);
          if (args->multiset_reduction.value)
            mu_Chan3.MultisetSort();
          mu_Chan2.Permute(Perm,0);
          if (args->multiset_reduction.value)
            mu_Chan2.MultisetSort();
          mu_Chan1.Permute(Perm,0);
          if (args->multiset_reduction.value)
            mu_Chan1.MultisetSort();
          mu_Cache.Permute(Perm,0);
          if (args->multiset_reduction.value)
            mu_Cache.MultisetSort();
        if (p.compare(workingstate)) {
          StateCopy(workingstate,&temp); return TRUE; }

        while (Perm.NextPermutation())
          {
            if (ns != workingstate)
              StateCopy(workingstate, ns);
              
              mu_CurCmd.Permute(Perm,0);
              if (args->multiset_reduction.value)
                mu_CurCmd.MultisetSort();
              mu_ExGntd.Permute(Perm,0);
              if (args->multiset_reduction.value)
                mu_ExGntd.MultisetSort();
              mu_CurPtr.Permute(Perm,0);
              if (args->multiset_reduction.value)
                mu_CurPtr.MultisetSort();
              mu_ShrSet.Permute(Perm,0);
              if (args->multiset_reduction.value)
                mu_ShrSet.MultisetSort();
              mu_InvSet.Permute(Perm,0);
              if (args->multiset_reduction.value)
                mu_InvSet.MultisetSort();
              mu_Chan3.Permute(Perm,0);
              if (args->multiset_reduction.value)
                mu_Chan3.MultisetSort();
              mu_Chan2.Permute(Perm,0);
              if (args->multiset_reduction.value)
                mu_Chan2.MultisetSort();
              mu_Chan1.Permute(Perm,0);
              if (args->multiset_reduction.value)
                mu_Chan1.MultisetSort();
              mu_Cache.Permute(Perm,0);
              if (args->multiset_reduction.value)
                mu_Cache.MultisetSort();
            if (p.compare(workingstate)) {
              StateCopy(workingstate,&temp); return TRUE; }
          }
        StateCopy(workingstate,&temp);
        return FALSE;
      }
    }
  if (!args->symmetry_reduction.value
      && args->multiset_reduction.value)
    {
      if (ns != workingstate)
          StateCopy(workingstate, ns);
      mu_CurCmd.MultisetSort();
      mu_ExGntd.MultisetSort();
      mu_CurPtr.MultisetSort();
      mu_ShrSet.MultisetSort();
      mu_InvSet.MultisetSort();
      mu_Chan3.MultisetSort();
      mu_Chan2.MultisetSort();
      mu_Chan1.MultisetSort();
      mu_Cache.MultisetSort();
      if (p.compare(workingstate)) {
        StateCopy(workingstate,&temp); return TRUE; }
      StateCopy(workingstate,&temp);
      return FALSE;
    }
  return (p.compare(ns));
}

/********************
 Canonicalization by fast exhaustive generation of
 all permutations
 ********************/
void SymmetryClass::Exhaustive_Fast_Canonicalize(state* s)
{
  int i;
  static state temp;
  Perm.ResetToExplicit();

  StateCopy(&temp, workingstate);
  ResetBestResult();
  for (i=0; i<Perm.count; i++)
    if (Perm.In(i))
      {
        StateCopy(workingstate, &temp);
        mu_CurCmd.Permute(Perm,i);
        if (args->multiset_reduction.value)
          mu_CurCmd.MultisetSort();
        SetBestResult(i, workingstate);
      }
  StateCopy(workingstate, &BestPermutedState);

  StateCopy(&temp, workingstate);
  ResetBestResult();
  for (i=0; i<Perm.count; i++)
    if (Perm.In(i))
      {
        StateCopy(workingstate, &temp);
        mu_ExGntd.Permute(Perm,i);
        if (args->multiset_reduction.value)
          mu_ExGntd.MultisetSort();
        SetBestResult(i, workingstate);
      }
  StateCopy(workingstate, &BestPermutedState);

  StateCopy(&temp, workingstate);
  ResetBestResult();
  for (i=0; i<Perm.count; i++)
    if (Perm.In(i))
      {
        StateCopy(workingstate, &temp);
        mu_CurPtr.Permute(Perm,i);
        if (args->multiset_reduction.value)
          mu_CurPtr.MultisetSort();
        SetBestResult(i, workingstate);
      }
  StateCopy(workingstate, &BestPermutedState);

  StateCopy(&temp, workingstate);
  ResetBestResult();
  for (i=0; i<Perm.count; i++)
    if (Perm.In(i))
      {
        StateCopy(workingstate, &temp);
        mu_ShrSet.Permute(Perm,i);
        if (args->multiset_reduction.value)
          mu_ShrSet.MultisetSort();
        SetBestResult(i, workingstate);
      }
  StateCopy(workingstate, &BestPermutedState);

  StateCopy(&temp, workingstate);
  ResetBestResult();
  for (i=0; i<Perm.count; i++)
    if (Perm.In(i))
      {
        StateCopy(workingstate, &temp);
        mu_InvSet.Permute(Perm,i);
        if (args->multiset_reduction.value)
          mu_InvSet.MultisetSort();
        SetBestResult(i, workingstate);
      }
  StateCopy(workingstate, &BestPermutedState);

  StateCopy(&temp, workingstate);
  ResetBestResult();
  for (i=0; i<Perm.count; i++)
    if (Perm.In(i))
      {
        StateCopy(workingstate, &temp);
        mu_Chan3.Permute(Perm,i);
        if (args->multiset_reduction.value)
          mu_Chan3.MultisetSort();
        SetBestResult(i, workingstate);
      }
  StateCopy(workingstate, &BestPermutedState);

  StateCopy(&temp, workingstate);
  ResetBestResult();
  for (i=0; i<Perm.count; i++)
    if (Perm.In(i))
      {
        StateCopy(workingstate, &temp);
        mu_Chan2.Permute(Perm,i);
        if (args->multiset_reduction.value)
          mu_Chan2.MultisetSort();
        SetBestResult(i, workingstate);
      }
  StateCopy(workingstate, &BestPermutedState);

  StateCopy(&temp, workingstate);
  ResetBestResult();
  for (i=0; i<Perm.count; i++)
    if (Perm.In(i))
      {
        StateCopy(workingstate, &temp);
        mu_Chan1.Permute(Perm,i);
        if (args->multiset_reduction.value)
          mu_Chan1.MultisetSort();
        SetBestResult(i, workingstate);
      }
  StateCopy(workingstate, &BestPermutedState);

  StateCopy(&temp, workingstate);
  ResetBestResult();
  for (i=0; i<Perm.count; i++)
    if (Perm.In(i))
      {
        StateCopy(workingstate, &temp);
        mu_Cache.Permute(Perm,i);
        if (args->multiset_reduction.value)
          mu_Cache.MultisetSort();
        SetBestResult(i, workingstate);
      }
  StateCopy(workingstate, &BestPermutedState);

};

/********************
 Canonicalization by fast simple variable canonicalization,
 fast simple scalarset array canonicalization,
 fast restriction on permutation set with simple scalarset array of scalarset,
 and fast exhaustive generation of
 all permutations for other variables
 ********************/
void SymmetryClass::Heuristic_Fast_Canonicalize(state* s)
{
  int i;
  static state temp;

  Perm.ResetToSimple();

  mu_CurPtr.SimpleCanonicalize(Perm);

  mu_ShrSet.Canonicalize(Perm);

  mu_InvSet.Canonicalize(Perm);

  mu_Chan3.Canonicalize(Perm);

  mu_Chan2.Canonicalize(Perm);

  mu_Chan1.Canonicalize(Perm);

  mu_Cache.Canonicalize(Perm);

};

/********************
 Canonicalization by fast simple variable canonicalization,
 fast simple scalarset array canonicalization,
 fast restriction on permutation set with simple scalarset array of scalarset,
 and fast exhaustive generation of
 all permutations for other variables
 and use less local memory
 ********************/
void SymmetryClass::Heuristic_Small_Mem_Canonicalize(state* s)
{
  unsigned long cycle;
  static state temp;

  Perm.ResetToSimple();

  mu_CurPtr.SimpleCanonicalize(Perm);

  mu_ShrSet.Canonicalize(Perm);

  mu_InvSet.Canonicalize(Perm);

  mu_Chan3.Canonicalize(Perm);

  mu_Chan2.Canonicalize(Perm);

  mu_Chan1.Canonicalize(Perm);

  mu_Cache.Canonicalize(Perm);

};

/********************
 Normalization by fast simple variable canonicalization,
 fast simple scalarset array canonicalization,
 fast restriction on permutation set with simple scalarset array of scalarset,
 and for all other variables, pick any remaining permutation
 ********************/
void SymmetryClass::Heuristic_Fast_Normalize(state* s)
{
  int i;
  static state temp;

  Perm.ResetToSimple();

  mu_CurPtr.SimpleCanonicalize(Perm);

  mu_ShrSet.Canonicalize(Perm);

  mu_InvSet.Canonicalize(Perm);

  mu_Chan3.Canonicalize(Perm);

  mu_Chan2.Canonicalize(Perm);

  mu_Chan1.Canonicalize(Perm);

  mu_Cache.Canonicalize(Perm);

};

/********************
  Include
 ********************/
#include "mu_epilog.hpp"
