/* associative array */
void assoc_init(void);
item *assoc_find(const char *key, const size_t nkey);
#ifdef SKIPLIST
item *assoc_find_next(const char *key, const size_t nkey);
item *assoc_next(item *it);
int assoc_pick_random_levels(void);
#endif//SKIPLIST
int assoc_insert(item *item);
void assoc_delete(const char *key, const size_t nkey);
void do_assoc_move_next_bucket(void);
int start_assoc_maintenance_thread(void);
void stop_assoc_maintenance_thread(void);

